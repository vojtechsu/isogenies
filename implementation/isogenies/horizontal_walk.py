# Implementation based on the algorithms from Towards practical key exchangefrom ordinary
# -isogeny graphs by Luca De Feo1, Jean Kieffer, and Benjamin Smith

from sage.databases.db_modular_polynomials import ClassicalModularPolynomialDatabase
from isogenies.utils import *
from sage.rings.all import PolynomialRing, Integer, GF, ZZ
from sage.schemes.elliptic_curves.all import EllipticCurve, EllipticCurve_from_j


# Computes end point of a walk from curve E
# walk contains a list of triples (l,lam,k), each representing k steps along ideal (l,\pi-lam)
# algorithm = "Elkies" or "Velu", where "Velu" assumes p=-1 mod l for each l
def horizontal_walk(E, walk, algorithm="Elkies"):
    curve = E
    t = E.trace_of_frobenius()
    for l, lam, k in walk:
        if algorithm == "Velu":
            curve = velu_walk(curve, l, lam, k)
            if curve.trace_of_frobenius() != t:
                curve = curve.quadratic_twist()
        else:
            curve = elkies_walk(curve, l, lam, k)
            if curve.trace_of_frobenius() != t:
                curve = curve.quadratic_twist()
    return curve.j_invariant()


# Makes a first step from curve E along ideal (l,\pi-lam) using Elkies algorithm
# Returns j-invariant
def elkies_first_step(E, l, lam):
    q = E.base_field().order()
    lam = GF(l)(lam)
    Phi = ClassicalModularPolynomialDatabase()[l]
    x = PolynomialRing(E.base_field(), 'x').gen()
    f = Phi(x, E.j_invariant())
    j_1, j_2 = f.roots()[0][0], f.roots()[1][0]
    E1 = elkies_mod_poly(E, j_1, l)
    try:
        I = EllipticCurveIsogeny(E, None, E1, l)
    except:
        I = l_isogeny(E, E1, l)
    r = lam.multiplicative_order()
    k = GF(q ** r)
    ext = extend_field(E, r)
    try:
        P = ext.lift_x(I.kernel_polynomial().any_root(k))
    except:
        return j_2
    if ext(P[0] ** q, P[1] ** q) == Integer(lam) * P:
        return j_1
    else:
        return j_2


# Makes another (not first) step from j_1 along ideal (l,\pi-lam) using Elkies algorithm
# j_0 is previous vertex
# Returns j-invariant
def elkies_next_step(j_0, j_1, l, lam):
    Phi = ClassicalModularPolynomialDatabase()[l]
    R = PolynomialRing(j_0.parent(), 'x')
    x = R.gen()
    f = R(Phi(x, j_1) / (x - j_0))
    return f.roots()[0][0]


# Makes a complete walk of k steps from curve E along ideal (l,\pi-lam) using Elkies algorithm
# Returns elliptic curve
def elkies_walk(E, l, lam, k):
    j_0 = E.j_invariant()
    if k == 0:
        return E
    lam = GF(l)(lam)
    q = E.base_field().order()
    mu = GF(l)(lam ** (-1) * q)
    if k < 0:
        return elkies_walk(E.quadratic_twist(), l, -mu, -k)
    j_1 = elkies_first_step(E, l, lam)
    for i in range(2, k + 1):
        j_0, j_1 = j_1, elkies_next_step(j_0, j_1, l, lam)
    return EllipticCurve_from_j(j_1)


# Makes a step from curve E along ideal (l,\pi-lam) using Velu algorithm
# Assumes that p=-1 mod l
# Returns elliptic curve
def velu_step(E, l, lam, order, q):
    Q = l_order_point(E, order, l)
    if lam.lift() * Q == E(Q[0] ** q, Q[1] ** q):
        return E.isogeny_codomain(Q)
    return None


# Makes a complete walk of k steps from curve E along ideal (l,\pi-lam) using Velu algorithm
# Assumes that p=-1 mod l
# Returns elliptic curve
def velu_walk(E, l, lam, k):
    q = E.base_field().order()
    lam = GF(l)(lam)
    r = lam.multiplicative_order()
    mu = GF(l)((lam ** (-1)) * q)
    r_mu = mu.multiplicative_order()
    if k < 0:
        return velu_walk(E.quadratic_twist(), l, -mu, -k)
    if r_mu == r:
        print("Invalid parameters")
        return
    if r_mu < r:
        return velu_walk(E.quadratic_twist(), l, -lam, k)
    t = E.trace_of_frobenius()
    order = rec_order(q, t, r)
    cur = extend_field(E, r)
    for i in range(k):
        cur = velu_step(cur, l, lam, order, q)
    cur = EllipticCurve_from_j(GF(q)(cur.j_invariant()))
    return cur

def walk_the_crater(E,l,lam):
    k = E.base_field()
    q = k.order()
    lam = GF(l)(lam)
    r = lam.multiplicative_order()
    t = E.trace_of_frobenius()
    order = rec_order(q, t, r)
    cur = extend_field(E, r)
    crater = [E.j_invariant()]
    cur = velu_step(cur, l, lam, order, q)
    while k(cur.j_invariant())!=E.j_invariant():
        crater.append(k(cur.j_invariant()))
        cur = velu_step(cur, l, lam, order, q)
    return crater