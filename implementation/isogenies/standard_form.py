from sage.rings.all import PolynomialRing, Integer, GF
from sage.schemes.elliptic_curves.all import EllipticCurve


# Functions that reduce tuple of rational maps from elliptic curve E to standard form (u(x)/v(x),s(x)/t(x)*y)
# Assuming that the characteristic of the base field of E is not 2 or 3


# Reduces polynomial #poly modulo curve equation of curve E, i.e. replaces y**2 by x**3+ax+b
def reduce_mod_curve(poly, E):
    Q = PolynomialRing(E.base_field(), ['x', 'y'])
    x, y = Q.gens()
    a, b = E.a4(), E.a6()
    equation = x ** 3 + a * x + b
    exponents = poly.exponents()  # list of (i,j) for each term x**i*y**j in poly
    for e_x, e_y in exponents:
        if e_y < 2:
            continue
        coef = poly.coefficient({x: e_x, y: e_y})
        e = e_y % 2
        poly -= coef * x ** (e_x) * y ** (e_y)
        poly += coef * x ** (e_x) * y ** e * equation ** ((e_y // 2))
    return poly


# For given rational functions f=(u(x)/v(x), s(x)/t(x)*y) divides both fractions by leading coefficients of u, s
def normalize_map(f, E):
    Q = PolynomialRing(E.base_field(), ['x', 'y'])
    x, y = Q.gens()
    u, v = f[0].numerator(), f[0].denominator()
    s, t = f[1].numerator(), f[1].denominator()
    k = u.numerator().coefficient({x: u.numerator().degree(x)})
    if k != 0:
        u /= k
        v /= k
    l = s.numerator().coefficient({x: s.numerator().degree(x), y: 1})
    if l != 0:
        s /= l
        t /= l
    return u / v, s / t


# Transforms isogeny(=tuple of rational maps) to its standard form (u(x)/v(x), s(x)/t(x)*y)
def standard_form(f, E):
    Q = PolynomialRing(E.base_field(), ['x', 'y'])
    y = Q.gen()
    u, v = Q(f[0].numerator()), Q(f[0].denominator())
    deg = v.degree(y)
    if deg % 2 == 1:
        u *= y
        v *= y
    v = reduce_mod_curve(v, E)
    u = reduce_mod_curve(u, E)
    s, t = Q(f[1].numerator()), Q(f[1].denominator())
    deg = t.degree(y)
    if deg % 2 == 1:
        s *= y
        t *= y
    t = reduce_mod_curve(t, E)
    s = reduce_mod_curve(s, E)
    return normalize_map((u / v, s / t), E)
