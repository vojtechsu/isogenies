from sage.rings.all import PolynomialRing, Integer, GF, ZZ
from sage.schemes.elliptic_curves.all import EllipticCurve
from libr.standard_form import standard_form
from sage.databases.db_modular_polynomials import ClassicalModularPolynomialDatabase


# Some useful functions used in implementing isogenies

# Computes the kernel polynomial from the kernel points
def kernel_polynomial_from_kernel(E, kernel):
    R_ext = PolynomialRing(kernel[0].curve().base_field(), 'x')
    x = R_ext.gen()
    f = 1
    for P in kernel:
        f *= (x - P[0])
    R = PolynomialRing(E.base_field(), 'x')
    f = R(f / f.gcd(f.derivative()))
    f /= f.list()[len(f.list()) - 1]
    return f


# Assuming the polynomial f can be decomposed as f = frobenius**n*g where frobenius is the map (x,y)->(x**p,y**p)
# Returns g
def extract_frobenius_poly(E, f):
    p = E.base_field().characteristic()
    Q = PolynomialRing(E.base_field(), 'x')
    x = Q.gen()
    f = Q(f)
    if f.is_constant():
        return f
    monomials = [x ** (u.degree() // p) for u in f.monomials()]
    return sum([a[0] * a[1] for a in zip(f.coefficients(), monomials)])


# Every isogeny f can be decomposed into separable part f_s and a power of Frobenius morphism
# Returns the separable part f_s
# Assuming that f is in standard form
def extract_frobenius(E, f):
    Q = PolynomialRing(E.base_field(), 'x')
    R = PolynomialRing(E.base_field(), ['x', 'y'])
    x, y = R.gens()
    u, v = Q(f[0].numerator()), Q(f[0].denominator())
    s, t = R(f[1].numerator()), R(f[1].denominator())
    s = Q((s / y).numerator())
    r = 0
    while u.derivative() == 0:
        r += 1
        u = extract_frobenius_poly(E, u)
        v = extract_frobenius_poly(E, v)
        s = extract_frobenius_poly(E, s)
        t = extract_frobenius_poly(E, t)
    return (u / v, s * y / t), r


# Codomain of the r-power Frobenius morphism
def frobenius_image_curve(E, r):
    p = E.base_field().characteristic()
    return EllipticCurve(E.base_field(), [E.a4() ** (p ** r), E.a6() ** (p ** r)])


# Returns Frobenius endomorphism on E
def frobenius(E):
    Q = PolynomialRing(E.base_ring(), ['x', 'y'])
    x, y = Q.gens()
    R = Q.fraction_field()
    q = E.base_ring().order()
    return R(x ** q), R(y ** q)


# Returns kernel polynomial from a tuple of rational maps
# Assuming that f is in standard form
def kernel_polynomial_from_maps(E, f):
    v = f[0]
    R = PolynomialRing(E.base_ring(), 'x')
    v = R(v.denominator())
    v = R(v / v.gcd(v.derivative()))
    v /= v.list()[len(v.list()) - 1]
    return v


# Returns the degree of tuple of maps
# Assuming that f is in standard form
def degree_from_maps(E, f):
    Q = f[0].numerator().parent()
    if f == 0:
        return 0
    u, v = Q(f[0].numerator()), Q(f[0].denominator())
    if u.is_constant():
        return v.degree()
    if v.is_constant():
        return u.degree()
    return max(v.degree(), u.degree())


# Returns kernel polynomial of multiplication by n
def torsion_poly(E, n):
    f = E.multiplication_by_m(n)
    return kernel_polynomial_from_maps(E, f)


# Finds all roots of polynomial v and extension of base field of E over which v splits
# Oficial implementation seems to be missing and/or have some issues
# Returns the roots and extended curve
def poly_to_set(E, v):
    q = E.base_field().order()
    deg = v.degree()
    e = 1
    R = PolynomialRing(GF(q), 'x')
    f = R(v)
    roots = f.roots()
    while len(roots) != deg:
        e += 1
        s = q ** e
        R = PolynomialRing(GF(s), 'x')
        f = R(v)
        roots = f.roots()
    roots = [r[0] for r in roots]
    ext_E = extend_field(E, e)

    ee = 1
    while True:
        Y = False
        for c in roots:
            if not ext_E.is_x_coord(c):
                Y = True
                break

        if Y:
            ee += 1
            s = ee * e
            R = PolynomialRing(GF(q ** (s)), 'x')
            f = R(v)
            roots = [r[0] for r in f.roots()]
            ext_E = extend_field(E, s)
        else:
            break

    return roots, ext_E


# Computes a set of points over extension of E which are defined by polynomial v
# (i.e. the x-coordinates are the roots of v)
# Returns the set of points and the extended curve
def kernel_set(E, v):
    xs, E_ext = poly_to_set(E, v)
    result = list()
    for x in xs:
        P = E_ext.lift_x(x, all=True)
        if len(P) == 2:
            result.append(P[0])
            result.append(P[1])
        else:
            result.append(P[0])
    return result, E_ext


# Returns the full n-torsion set of curve E (points are defined over some extension)
# Returns the set and the extended curve
def torsion_set(E, n):
    v = torsion_poly(E, n)
    return kernel_set(E, v)


# Returns the full l-torsion set, for l prime, of curve E (points are defined over some extension)
# Returns the set and the extended curve
def torsion_set_prime(E, l):
    p = E.base_field().order()
    k = torsion_finder(E, l)
    field = GF(p ** k)
    Ext = extend_field(E, k)
    v = torsion_poly(E, l)
    torsion = []
    for x in v.roots(field):

        P = Ext.lift_x(x, all=True)
        if len(P) == 2:
            result.append(P[0])
            result.append(P[1])
        else:
            result.append(P[0])
    return torsion, Ext


# Returns the n-torsion points that lie in given extension ext of E
def torsion_set_low(E, ext, n):
    v = torsion_poly(E, n)
    roots = [r[0] for r in v.roots(ext.base_field()) for _ in range(r[1])]
    result = []
    for r in roots:
        try:
            result.append(ext.lift_x(r))
        except:
            pass
    return result


# Returns isomorphism (tuple of rational maps) between E and iso_E
def isomorphism_isogeny(E, iso_E):
    field = E.base_field()
    iso_E = EllipticCurve(field, [field(iso_E.a4()), field(iso_E.a6())])
    isomorphism = E.isomorphism_to(iso_E)
    x, y = PolynomialRing(E.base_ring(), ['x', 'y']).gens()
    u, r, s, t = isomorphism.tuple()
    return u ** 2 * x + r, u ** 3 * y + s * u ** 2 * x + t


# Returns a r-power Frobenius morphism from E and its codomain
def r_frobenius_morphism(E, r):
    x, y = PolynomialRing(E.base_ring(), ['x', 'y']).gens()
    p = E.base_field().characteristic()
    a = E.a4() ** (p ** r)
    b = E.a6() ** (p ** r)
    return (x ** (p ** r), y ** (p ** r)), EllipticCurve(E.base_field(), [a, b])


# Add a tuple of maps in standard form using the addition formulas on elliptic curve
def add_maps(f, g, E):
    if f == 0:
        return g
    if g == 0:
        return f
    Q = PolynomialRing(E.base_ring(), ['x', 'y'])
    x, y = Q.gens()
    a = E.a4()
    b = E.a6()
    r = x ** 3 + a * x + b
    if f[0] != g[0]:
        m = (g[1] - f[1]) / (g[0] - f[0])
        sum_x = m ** 2 - f[0] - g[0]
        sum_y = m * (f[0] - sum_x) - f[1]
        return standard_form((sum_x, sum_y), E)
    if f[1] != g[1]:
        return 0
    if f == g and f[1] == 0:
        return 0
    if f == g and f[1] != 0:
        m = (3 * f[0] ** 2 + a) / (2 * f[1])
        sum_x = m ** 2 - 2 * f[0]
        sum_y = m * (f[0] - sum_x) - f[1]
        return standard_form((sum_x, sum_y), E)


# Computes trace of an extended curve using recursive formula t_n = t*t_(n-1)-q*t_(n-2)
def rec_trace(q, r, t):
    a = 2
    b = t
    for _ in range(r - 1):
        temp = b
        b = t * b - q * a
        a = temp
    return b


# computes order of extension using the recursive formula
def rec_order(q, t, r):
    a = 2
    b = t
    for _ in range(r - 1):
        temp = b
        b = t * b - q * a
        a = temp
    return q ** r + 1 - b


# computes the eigenvalues of Frobenius endomorphism and their multiplicative order
# Returns a list of tuples
def eigenvalues_with_orders(E, l):
    t = E.trace_of_frobenius()
    x = PolynomialRing(GF(l), 'x').gen()
    q = E.base_field().order()
    f = x ** 2 - t * x + q
    eigen = []
    for r in f.roots():
        eigen.append((r[0], r[0].multiplicative_order()))
    return eigen


# Decides whether the l-torsion of elliptic curve is bycyclic
def is_torsion_bicyclic(E, l):
    order = E.order()
    v = ZZ.valuation(l)
    n = v(order)
    if n < 2:
        return False
    D = E.trace_of_frobenius() ** 2 - 4 * E.base_field().order()
    if not (l ** 2).divides(D):
        return False
    Phi = ClassicalModularPolynomialDatabase()[l]
    x = PolynomialRing(E.base_field(), 'x').gen()
    return len(Phi(E.j_invariant(), x).roots()) > 2


# Computes the eigenvalues of Frobenius endomorphism in F_l, or in F_l if s=2
def eigenvalues(E, l, s=1):
    t = E.trace_of_frobenius()
    x = PolynomialRing(GF(l ** s), 'x').gen()
    q = E.base_field().order()
    f = x ** 2 - t * x + q
    return f.roots()


# Computes the minimal degree of extension of base field of elliptic curve in which lies the whole torsion
def torsion_finder(E, l):
    eig = eigenvalues(E, l)
    if not eig:
        eig = eigenvalues(E, l, s=2)
        a, b = eig[0][0], eig[1][0]
        return a.multiplicative_order().lcm(b.multiplicative_order())

    a = eig[0][0]
    if len(eig) == 2:
        b = eig[1][0]
        return a.multiplicative_order().lcm(b.multiplicative_order())

    k2 = a.multiplicative_order()
    q = E.base_ring().order()
    E_ext = extend_field(E, k2)
    if not is_torsion_bicyclic(E_ext, l):
        k2 *= l
    return k2


# Finds a point of prime order l, the order of the curve must be given in argument
def l_order_point(E, order, l):
    v = ZZ.valuation(l)
    factor = l ** v(order)
    P = (order // factor) * E.random_point()
    while P == E(0, 1, 0):
        P = (order // factor) * E.random_point()
    Q = l * P
    while Q != E(0, 1, 0):
        P = Q
        Q = l * P
    return P


# Returns a list of l-isogenous j-invariants to j, l-th modular polynomial can be given in Phi
# If multiplicity = False, then each j-invariant occurs the number of times given by its multiplicity as a root
# Otherwise resulting list is a list of tuples, where the second element is the multiplicity
def isogenous_curves(j, l=None, Phi=None, multiplicities=True, E=None):
    field = j.parent()
    x = PolynomialRing(field, 'x').gen()
    if Phi == None:
        Phi = ClassicalModularPolynomialDatabase()[l]
    f = Phi(x, j)
    if not multiplicities:
        if E == None:
            return [i[0] for i in f.roots() for _ in range(i[1])]
        return [(i[0], elkies_mod_poly(E, i[0], Phi.degree() // 2)) for i in f.roots() for _ in range(i[1])]
    return f.roots()


# Finds an isogeny from E to E2 using "isogenies_prime_degree" function
def l_isogeny(E, E2, l):
    j = E2.j_invariant()
    isog = E.isogenies_prime_degree(l)
    for i in isog:
        if i.codomain().j_invariant() == j:
            return i
    return None


# Finds the minimal degrees k_2,k_1,i_2,i_1 of extension of curve E/F_q where
# E/F_q**(k_2) - contains the full l-torsion, E/F_q**(k_1) - contains nontrivial l-torsion
# E/F_q**(i_2) - all l+1 isogenies are rational, E/F_q**(i_1) - at least 1 isogeny is rational
def ki_finder(E, l):
    eig = eigenvalues(E, l)
    if not eig:
        eig = eigenvalues(E, l, s=2)
        a, b = eig[0][0], eig[1][0]
        k2 = a.multiplicative_order().lcm(b.multiplicative_order())
        i2 = (a * b ** (-1)).multiplicative_order()
        i1 = i2
        k1 = k2
        return k2, k1, i2, i1

    a = eig[0][0]
    if len(eig) == 2:
        b = eig[1][0]
        k2 = a.multiplicative_order().lcm(b.multiplicative_order())
        k1 = min(a.multiplicative_order(), b.multiplicative_order())
        i1 = 1
        i2 = (a * b ** (-1)).multiplicative_order()
        return k2, k1, i2, i1

    k2 = a.multiplicative_order()
    k1 = a.multiplicative_order()
    i1 = 1
    i2 = 1
    q = E.base_ring().order()
    E_ext = extend_field(E, k2)
    if not is_torsion_bicyclic(E_ext, l):
        k2 *= l
        i2 *= l
    return k2, k1, i2, i1


# Computes the n-th discriminant polynomial, i.e. f_n(x) such that f_n(D) = D_n
# where D is the discriminant of Frobenius endomorphism and D_n is the discriminant of n-power Frobenius endomorphism
def discriminant_polynomial(E, n):
    q = E.base_field().order()
    d = PolynomialRing(ZZ, 'd').gen()
    s = 0
    for k in range(n):
        s += binomial(2 * n - k - 1, k) * n // (n - k) * d ** (n - k) * q ** k
    return s


# Computes the discriminant of Frobenius endomorphism
def discriminant(E):
    t = E.trace_of_frobenius()
    q = E.base_field().order()
    print("ahoj")
    return t ** 2 - 4 * q


# Extends base field of E with degree of extension r
def extend_field(E, r):
    q = E.base_field().order()
    field = GF(q ** r)
    a = field(E.a4())
    b = field(E.a6())
    return EllipticCurve(field, [a, b])


# Computes elliptic curve which is l-isogenous to E given j-invariant j2 of the desired curve
def elkies_mod_poly(E, j2, l):
    j = E.j_invariant()
    Phi = ClassicalModularPolynomialDatabase()[l]
    x = PolynomialRing(E.base_field(), 'x').gen()
    f = Phi(j2, x)
    F1 = f.derivative()(j)
    g = Phi(j, x)
    F2 = g.derivative()(j2)
    try:
        lam = E.a6() / E.a4() * F1 / F2 * j * (-18) / l
        aa = -lam ** 2 / (j2 * (j2 - 1728) * l ** 4 * 48)
        bb = -lam ** 3 / (j2 ** 2 * (j2 - 1728) * l ** 6 * 864)
        return EllipticCurve(E.base_field(), [aa, bb])
    except:
        return None
