# Functions for computing trace of Frobenius using Schoof's algorithm and isogeny volcanoes based on
# Isogeny Volcanoes and the SEA Algorithm by Mireille Fouquet and François Morain
# (https://link.springer.com/chapter/10.1007/3-540-45455-1_23)
# Algorithm for l=2 is added

from sage.rings.finite_rings.integer_mod import IntegerMod
from sage.rings.finite_rings.integer_mod import mod
from sage.rings.all import PolynomialRing, Integer, GF, ZZ
from sage.arith.misc import gcd, next_prime, CRT_list
from sage.rings.all import PolynomialRing
from sage.rings.finite_rings.integer_mod_ring import crt
from libr.endomorphism_schoof import trace_of_frobenius_mod_2, trace_of_frobenius_mod, prod
from libr.volcano_depth import find_full_descending_paths, Found_0_1728
from sage.functions.all import sqrt


# Returns true if order of E is divisible by 8
def is_8_order(E):
    Q = PolynomialRing(E.base_field(), 'x')
    x = Q.gen()
    A = E.a4()
    B = E.a6()
    f = -x ** 6 - 5 * A * x ** 4 + 5 * A ** 2 * x ** 2 - 20 * B * x ** 3 + A ** 3 + 4 * A * B * x + 8 * B ** 2
    counter = 0
    for r in f.roots():
        try:
            P = E.lift_x(r[0])
            counter += 1
            g = -x ** 4 + 2 * A * x ** 2 - A ** 2 + 8 * B * x + 4 * (x ** 3 + A * x + B) * P[0]
            for s in g.roots():
                y1 = (2 * P[1]) ** (-1) * ((3 * s[0] ** 2 + A) * (s[0] - P[0]) - 2 * (s[0] ** 3 + A * s[0] + B))
                Q = E(s[0], y1)
                return True
        except:
            pass
    return counter >= 4


# Computes trace modulo l**(2n) with n being depth of volcano (except for case l=2)
# If volcano_2 = True the function uses our algorithm for l=2, otherwise it is simply Fouquet and Morain style algorithm
def finding_t_modln(E, l, volcano_2=True):
    field = E.base_field()
    q = E.base_field().order()
    j = E.j_invariant()

    if l == 2:
        mod_l = trace_of_frobenius_mod_2(E)
    else:
        mod_l = trace_of_frobenius_mod(E, l)

    # computes depth of volcano modulo l
    if mod(mod_l ** 2, l) != mod(4 * q, l):
        return mod_l, l
    try:
        result = find_full_descending_paths(j, l)
    except Found_0_1728:
        return mod_l, l
    if len(result) == 1:
        return mod_l, l

    n = result[3]
    e = result[2]

    modul = l ** (2 * n)
    if e == 0:
        modul *= l
    if l == 2 and not volcano_2:
        if modul < 2 ** 3:
            return mod_l, 2
        else:
            return 2, 4

    if l == 2:
        if modul < 2 ** 3:
            return mod_l, 2
        if modul < 2 ** 5 or q % 8 == 3 or q % 8 == 7:
            return 2, 4
        roots = mod(4 * q, modul).sqrt(all=True)
        roots = [Integer(r % (modul // 4)) for r in roots]
        if is_8_order(E):
            for r in roots:
                if q % 8 == 1 and r % 8 == 2:
                    return r, Integer(modul // 4)
                if q % 8 == 5 and r % 8 == 6:
                    return r, Integer(modul // 4)
        else:
            for r in roots:
                if q % 8 == 5 and r % 8 == 2:
                    return r, Integer(modul // 4)
                if q % 8 == 1 and r % 8 == 6:
                    return r, Integer(modul // 4)

    root = Integer(mod(4 * q, modul).sqrt())

    if mod(root, l) == mod(mod_l, l):
        return root, modul
    else:
        return modul - root, modul


# Compute trace of Frobenius endomorphism of E
def volcano_schoof(E, volcano_2 = True):
    q = E.base_field().order()
    residues = []
    moduli = []
    l = 2
    while prod(moduli) <= 4 * sqrt(q):
        if q % l == 0:
            l = next_prime(l)
        res = finding_t_modln(E, l, volcano_2 = volcano_2)
        residues.append(res[0])
        moduli.append(res[1])
        l = next_prime(l)
    t = CRT_list(residues, moduli)
    if t > 2 * sqrt(q):
        t = t - prod(moduli)
    return t
