# Implementation of algorithms from Isogeny Volcanoes and the SEA Algorithm by Mireille Fouquet and François Morain
# https://link.springer.com/chapter/10.1007/3-540-45455-1_23

from isogenies.utils import *
from sage.calculus.functional import derivative


class Found_0_1728(UserWarning):
    '''Raised when special curve is found'''
    pass


# Determines if j-invariant is special, i.e. equal to 0,1728, we also call a curve special if the modular polynomial Phi(j,x) is not separable, see the paper for further info
def special_curve(j, Phi):
    field = j.parent()
    if j == field(0) or j == field(1728):
        return True
    x = PolynomialRing(field, 'x').gen()
    f = Phi(x, j)
    der = derivative(f, x)
    return f.gcd(der) != 1


# Returns a descending path (list) from j to a leaf, with no special curves
# Assumes the j is not special
# If special curve is found then an exception is raised iff argument special = True
def find_descending_path(j, Phi, l, special=False):
    field = j.parent()

    neighb = isogenous_curves(j, Phi=Phi, multiplicities=False)
    if not neighb:  # no l-isogenies from j
        return list()

    if len(neighb) < 3:
        return [j]

    paths = [[j, neighb[0]], [j, neighb[1]], [j, neighb[2]]]

    cur = [j, j, j]
    nex = [neighb[0], neighb[1], neighb[2]]

    S = list()  # neighbors of neighbors
    for i in range(3):
        if not special_curve(nex[i], Phi):
            S.append(isogenous_curves(nex[i], Phi=Phi, multiplicities=False))
        else:
            S.append(list())
            if special:
                raise Found_0_1728

    while True:
        for i in range(3):
            if not S[i]:  # nex[i] is special
                if special:
                    raise Found_0_1728
                continue
            if len(S[i]) == 1:  # nex[i] is a leaf
                return paths[i]
            else:
                tmp = cur[i]
                cur[i] = nex[i]
                # if first neighbor of nex[i] is current curve, pick other
                if S[i][0] == tmp:
                    nex[i] = S[i][1]
                else:

                    nex[i] = S[i][0]

                paths[i].append(nex[i])  # extend path by next curve
                if special_curve(nex[i], Phi):
                    S[i] = list()
                    if special:
                        raise Found_0_1728
                else:
                    S[i] = isogenous_curves(nex[i], Phi=Phi, multiplicities=False)


# paths is a list of descending paths starting at neighbours of j
# Returns e,m,length,fullpaths where fullpaths is a list of some full descending paths and
# 1) e=0, length=|fullpaths[m]| is maximal
# 2) e=(d/l), m=-1 and length is the depth of the volcano if j is in the crater
def detect_surface(paths, j, l):
    e = 0
    fullpaths = list()

    # finds m such that length of paths[m] is maximal
    m = 0
    for i in range(len(paths)):
        if len(paths[i]) > len(paths[m]):
            m = i

    # find all i such that paths[i] is maximal
    max_paths = list()
    for i in range(len(paths)):
        if len(paths[i]) == len(paths[m]) and m != i:
            max_paths.append(i)

    # j is in the crater alone
    if len(max_paths) == l:
        paths[0].insert(0, j)
        return -1, -1, len(paths[m]) - 1, [paths[0]]

    # j is in circular crater
    if len(max_paths) == 1:
        mm = max_paths[0]
        # now find index r distinct from m and mm
        if m == 0 or mm == 0:
            if m == 1 or mm == 1:
                r = 2
            else:
                r = 1
        else:
            r = 0

        paths[r].insert(0, j)
        fullpaths = [paths[r], paths[m], paths[mm]]
        return 1, -1, len(paths[m]) - 1, fullpaths

    if not max_paths:
        if m == 0:
            r = 1
        else:
            r = 0

            # j is in the crater with one other curve
        if len(paths[m]) - len(paths[r]) == 1:
            e = 0
            length = len(paths[m]) - 1
            paths[r].insert(0, j)
            fullpaths = [paths[r], paths[m]]
            m = -1
        # j is not in the crater
        else:
            length = len(paths[m]) - 1

    return e, m, length, fullpaths


# Input: j = j-invariant of a curve E, l = degree of isogeny
# Returns [crater,ascend,e,depth,fullpaths], crater = curve on the crater
# above E, ascend = path to crater, e = type of crater, depth = depth of #crater,
# fullpaths = list of some full descending paths

def find_full_descending_paths(j, l, special=True):
    field = j.parent()
    Phi = ClassicalModularPolynomialDatabase()[l]

    if special_curve(j, Phi) and special:
        raise Found_0_1728

    neighb = isogenous_curves(j, Phi=Phi, multiplicities=False)

    if not neighb:
        return ['n']  # no l-isogenies from j
    if len(neighb) == 2 and neighb[0] == neighb[1] and neighb[0] == j:
        return [2]  # trivial volcano with 2 self-loops
    if len(neighb) == 1 and neighb[0] == j:
        return [1]  # trivial volcano with 1 self-loop
    if len(neighb) == 2 and neighb[0] == neighb[1]:
        return [3]  # two points with two segments
    if len(neighb) == 2:
        return [5]  # open crater with zero depth

    cur = j
    ascend = [j]

    # if j is a leaf, then we take its parent
    if len(neighb) == 1:
        cur = neighb[0]
        if len(isogenous_curves(cur, Phi=Phi, multiplicities=False)) == 1:
            return [4]  # single segment
        else:
            ascend.append(neighb[0])

    det_sur = 0
    B = list()
    counter = 0

    while det_sur != -1:
        F = isogenous_curves(cur, Phi=Phi, multiplicities=False)

        for i in range(l + 1):
            if special_curve(F[i], Phi) and special:
                raise Found_0_1728
            path = find_descending_path(F[i], Phi, l)
            if counter == 1:
                B[i] = path
            else:
                B.append(path)
        e, det_sur, depth, fullpaths = detect_surface(B, cur, l)
        if det_sur != -1:
            cur = F[det_sur]
            ascend.append(cur)
        counter = 1

    return [cur, ascend, e, depth, fullpaths]


# Computes the depth of l-volcano of E using the functions above
def volcano_depth(E, l):
    j = E.j_invariant()
    try:
        res = find_full_descending_paths(j, l)
        if len(res) == 1:
            return 0
        return res[3]
    except Found_0_1728:
        print("Curve with j_invariant 0 or 1728 found")
        return -1
