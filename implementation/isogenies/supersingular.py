# Algorithm for supersingularity identification based on floor finding in volcanoes
# From paper https://arxiv.org/pdf/1107.1140.pdf  page 6

from sage.rings.all import PolynomialRing, Integer, GF
from sage.schemes.elliptic_curves.all import EllipticCurve
from sage.databases.db_modular_polynomials import ClassicalModularPolynomialDatabase
from sage.functions.all import floor, log


# Decides whether E is supesingular (True/False)
def is_supersingular(E):
    p = E.base_field().characteristic()
    j = E.j_invariant()
    if not j in GF(p ** 2):
        return False
    if p <= 3:
        return j == 0
    F = ClassicalModularPolynomialDatabase()[2]
    x = PolynomialRing(GF(p ** 2), 'x').gen()
    f = F(x, j)
    roots = [i[0] for i in f.roots() for _ in range(i[1])]
    if len(roots) < 3:
        return False
    vertices = [j, j, j]
    m = floor(log(p, 2)) + 1
    for k in range(1, m + 1):
        for i in range(3):
            f = F(x, roots[i])
            g = x - vertices[i]
            a = f.quo_rem(g)[0]
            vertices[i] = roots[i]
            attempt = a.roots()
            if len(attempt) == 0:
                return False
            roots[i] = attempt[0][0]
    return True
