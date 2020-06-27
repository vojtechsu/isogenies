# Implementing Velu algorithm from Elliptic Curves: Number Theory and Cryptography by Lawrence C. Washington
# Assuming characteristic of the base field of the ellipit curve is not 2 or 3
from sage.rings.all import PolynomialRing, Integer, GF
from sage.schemes.elliptic_curves.all import EllipticCurve
from libr.standard_form import standard_form


# Computes only codomain from kernel. The codomain will be defined over the same field
# as the kernel points, unless the domain curve is specified. In that case the function
# will try to define the codomain over the same field.
# One can provide the kernel set also as one element set, generating the entire kernel
def velu_codomain(kernel, domain=None):
    E = kernel[0].curve()
    R = []
    v = 0
    w = 0
    for P in kernel:
        g_x = 3 * P[0] ** 2 + E.a4()
        g_y = -2 * P[1]
        u_P = g_y ** 2
        if 2 * P == E(0, 1, 0):
            R.append(P)
            v_P = g_x
        else:
            if not -P in R:
                R.append(P)
                v_P = 2 * g_x
            else:
                continue

        v += v_P
        w += (u_P + P[0] * v_P)

    a = E.a4() - 5 * v
    b = E.a6() - 7 * w
    if domain != None:
        try:
            a = domain.base_field()(a)
            b = domain.base_field()(b)
            codomain = EllipticCurve(domain.base_field(), [a, b])
        except:

            codomain = EllipticCurve(E.base_field(), [a, b])
    else:
        codomain = EllipticCurve(E.base_field(), [a, b])
    return codomain


# Computes codomain and a pair of rational maps
def velu(kernel, domain=None):
    E = kernel[0].curve()
    Q = PolynomialRing(E.base_field(), ['x', 'y'])
    x, y = Q.gens()
    X = x
    Y = y
    R = []
    v = 0
    w = 0

    for P in kernel:

        g_x = 3 * P[0] ** 2 + E.a4()
        g_y = -2 * P[1]
        u_P = g_y ** 2
        if 2 * P == E(0, 1, 0):
            R.append(P)
            v_P = g_x
        else:
            if not -P in R:
                R.append(P)
                v_P = 2 * g_x
            else:
                continue

        v += v_P
        w += (u_P + P[0] * v_P)
        X += (v_P / (x - P[0]) + u_P / (x - P[0]) ** 2)
        Y -= (2 * u_P * y / (x - P[0]) ** 3 + v_P * (y - P[1]) / (x - P[0]) ** 2 - g_x * g_y / (x - P[0]) ** 2)

    a = E.a4() - 5 * v
    b = E.a6() - 7 * w
    if domain != None:
        try:

            a = domain.base_field()(a)
            b = domain.base_field()(b)
            codomain = EllipticCurve(domain.base_field(), [a, b])
            R = PolynomialRing(E.base_field(), ['x', 'y'])
            Rf = R.fraction_field()
            X = Rf(X)
            Y = Rf(Y)
            f = standard_form((X, Y), domain)
        except:

            codomain = EllipticCurve(E.base_field(), [a, b])
            f = standard_form((X, Y), E)
    else:
        codomain = EllipticCurve(E.base_field(), [a, b])
        f = standard_form((X, Y), E)
    return codomain, f
