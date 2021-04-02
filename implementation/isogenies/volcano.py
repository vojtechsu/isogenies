from isogenies.utils import *
from sage.graphs.all import Graph
from sage.schemes.elliptic_curves.all import EllipticCurve_from_j
from sage.arith.functions import lcm
from isogenies.horizontal_walk import walk_the_crater
from sage.plot.colors import rainbow

UPPER_BITS = 100
VELU = False
CRATER = None


class Volcano:

    # Class for l-volcano of elliptic curve E over finite field
    # We can construct Volcano either using Velu algorithm (Velu = True) or modular polynomials (Velu = False)

    # If Velu algorithm is chosen, constructor tries to find kernels of isogenies in extension,
    # if the size of the base field of extension is higher than upper_bit_limit, then the algorithm stops

    # In case of the option of modular polynomials, we assume that l<127
    # You can turn off the 0,1728 warning with special = False
    def __init__(self, E, l, Velu=False, upper_bit_limit=100, special=True):

        self._l = l
        self._E = E
        global VELU
        VELU = Velu

        global UPPER_BITS
        UPPER_BITS = upper_bit_limit

        self.field = E.base_field()

        try:
            self._neighbours, self._vertices, self._special = BFS(E.j_invariant(), l)

        except large_extension_error as e:
            print("Upper limit for bitlength of size of extension field exceeded")
            print(e.msg)
            return

        if self._special and special:
            print("Curve with j_invariant 0 or 1728 found, may malfunction.")
        self._depths = {}
        self._levels = []
        self._depth = 0
        self._graph = Graph(multiedges=True, loops=True)
        for s in self._neighbours.values():
            self._graph.add_vertex(s[0])

        for s in self._neighbours.values():
            for i in range(1, len(s)):
                if not self._graph.has_edge(s[0], s[i][0]):
                    for j in range(s[i][1]):
                        self._graph.add_edge((s[0], s[i][0], j))
        if len(self._vertices) > 1 and E.is_ordinary():
            self.compute_depths()
        else:
            self._depths = {str(E.j_invariant()): 0}
            self._levels = [self._vertices]

    # Method for computing depths and sorting vertices into levels
    def compute_depths(self):
        heights = {}
        level = []

        if len(list(self._neighbours.values())[0]) == 3:
            self._levels = [self._vertices]
            self._depths = {str(i): 0 for i in self._vertices}
            self._depth = 0
            return

        for s in self._neighbours.keys():
            if len(self._neighbours[s]) == 2:
                heights[s] = 0
                level.append(self._neighbours[s][0])

        self._levels.append(level)
        h = 1
        while len(heights.keys()) != len(self._vertices):

            level = []
            for s in self._neighbours.keys():

                if s in heights.keys():
                    continue
                if len(self._neighbours[s]) > 2:
                    if str(self._neighbours[s][1][0]) in heights.keys() and heights[
                        str(self._neighbours[s][1][0])] == h - 1:
                        heights[s] = h
                        level.append(self._neighbours[s][0])

                        continue

                    if str(self._neighbours[s][2][0]) in heights.keys() and heights[
                        str(self._neighbours[s][2][0])] == h - 1:
                        heights[s] = h
                        level.append(self._neighbours[s][0])

                        continue

                if len(self._neighbours[s]) > 3:
                    if str(self._neighbours[s][3][0]) in heights.keys() and heights[
                        str(self._neighbours[s][3][0])] == h - 1:
                        heights[s] = h
                        level.append(self._neighbours[s][0])

                        continue
            h += 1
            self._levels.append(level)

        self._depth = h - 1
        self._depths = {}
        for k in heights.keys():
            self._depths[k] = h-1-heights[k]
        self._levels.reverse()

    # Returns the defining degree of volcano
    def degree(self):
        return self._l

    # Returns the level at depth i
    def level(self, i):
        return self._levels[i]

    # Returns list of all edges
    def edges(self):
        return self._graph.edges()

    # Returns depth of volcano
    def depth(self):
        return self._depth

    # Returns the crater of volcano
    def crater(self):
        return self._levels[0]

    # Plots the volcano
    # Optional arguments figsize, vertex_size, vertex_labels and layout which are the same as in igraph (sage Class)
    def plot(self, figsize=None, vertex_labels=True, vertex_size=None, layout=None):
        try:
            self._graph.layout(layout=layout, save_pos=True)
        except:
            pass
        if vertex_size != None:
            return self._graph.plot(figsize=figsize, vertex_labels=vertex_labels, vertex_size=vertex_size)
        else:
            return self._graph.plot(figsize=figsize, vertex_labels=vertex_labels)

    # Returns all vertices of volcano
    def vertices(self):
        return self._vertices

    # Returns all neighbours of vertex j
    def neighbors(self, j):
        return self._neighbours[str(j)][1:]

    # Returns depth of vertex j
    def vertex_depth(self, j):
        return self._depths[str(j)]

    # Returns true if the volcano contains vertex 1728 or 0
    def special(self):
        return self._special

    # Returns parent (upper level neighbour) of j
    def volcano_parent(self, j):
        h = self._depths[str(j)]
        for i in self._neighbours[str(j)][1:]:
            if self._depths[str(i[0])] < h:
                return i[0]
        return None

    # Returns all children (lower level neighbours) of vertex j
    def volcano_children(self, j):
        children = []
        h = self._depths[str(j)]
        for i in self._neighbours[str(j)][1:]:
            if self._depths[str(i[0])] > h:
                children.append(i[0])
        return children

    # Finds an extension of curve over which the volcano has depth h
    def expand_volcano(self, h):
        return Volcano(expand_volcano(self._E, h, self._l), self._l)

    def __repr__(self):
        return "Isogeny %r-volcano of depth %r over %r" % (self._l, self.depth(), self.field)


# find neighbors of elliptic curve usign Velu algorithm
# Returns list of tuples (j-invariant,n) where n is number of edges connecting them
def isogenous_curve_velu(E, l, t=None):
    if t is None:
        t = E.trace_of_frobenius()
    q = E.base_field().order()
    field = E.base_field()

    eigenvalues = eigenvalues_with_orders(E, l)
    if not eigenvalues:
        return []
    if len(eigenvalues) == 2:
        
        r_1,r_2= eigenvalues[0][1], eigenvalues[1][1]
        lam, mu = eigenvalues[0][0],eigenvalues[1][0]

        if r_1!=r_2:
            global CRATER
            if CRATER == None:
                r,lam = (r_1,lam) if r_1<r_2 else (r_2,mu)
                if (q ** r).nbits() > UPPER_BITS:
                    msg = "%s>%s" % (str((q ** r).nbits()), str(UPPER_BITS))
                    raise large_extension_error(msg)
                    return None


                    
                crater = walk_the_crater(E,l,lam)
                CRATER = crater
            for i in range(len(CRATER)):
                if CRATER[i]==E.j_invariant():
                    if i==0:
                        j1 = CRATER[1]
                        j2 = CRATER[len(CRATER)-1]
                        break
                    if i==len(CRATER)-1:
                        j1 = CRATER[i-1]
                        j2 = CRATER[0]
                        break
                    if i>0 and i!=len(CRATER)-1:
                        j1 = CRATER[i-1]
                        j2 = CRATER[i+1]
                        break
            if j1 == j2:
                return [(j1, 2)]
            return [(j1, 1), (j2, 1)]
                        
        
            
        
        r = r_1
        if (q ** r).nbits() > UPPER_BITS:
            msg = "%s>%s" % (str((q ** r).nbits()), str(UPPER_BITS))
            raise large_extension_error(msg)
            return None
        div = E.division_polynomial(l)
        k = GF(q**r)
        ext = E.change_ring(k)
        roots = div.roots(k)
        j1,j2 = 0,0
        for a,b in roots:
            P = ext.lift_x(a)
            if j1==0 and Integer(lam)*P== ext(P[0]**q,P[1]**q):
                j1 = ext.isogeny(P).codomain().j_invariant()
                j1 = E.base_field()(j1)
            if j2==0 and Integer(mu)*P== ext(P[0]**q,P[1]**q):
                j2 = ext.isogeny(P).codomain().j_invariant()
                j2 = E.base_field()(j2)
        if j1 == j2:
            return [(j1, 2)]
        return [(j1, 1), (j2, 1)]

    lam = eigenvalues[0]
    r = lam[1]
    if (q ** r).nbits() > UPPER_BITS:
        msg = "%s>%s" % (str((q ** r).nbits()), str(UPPER_BITS))
        raise large_extension_error(msg)
        return None

    ext = extend_field(E, r)
    order = rec_order(q, t, r)
    P = l_order_point(ext, order, l)
    isg = ext.isogeny(P)
    if not (l ** 2).divides(order):
        return [(isg.codomain().j_invariant(), 1)]
    neighbours = [(isg.codomain().j_invariant(), 1)]
    R = PolynomialRing(E.base_field(), 'x')
    g = E.division_polynomial(l) / isg.kernel_polynomial()
    if not g in R:
        return [(isg.codomain().j_invariant(), 1)]
    f = R(g)
    try:
        z = f.any_root(ext.base_field())
    except ValueError:
        return [(isg.codomain().j_invariant(), 1)]
    Q = ext.lift_x(z)
    jQ = ext.isogeny(Q).codomain().j_invariant()
    if jQ == neighbours[0][0]:
        neighbours = [(jQ, 2)]
    else:
        neighbours.append((jQ, 1))
    R = P + Q
    for _ in range(l - 1):
        j = ext.isogeny(R).codomain().j_invariant()
        for n in neighbours:
            if j == n[0]:
                n[1] += 1
                R += Q
                continue
        if (j, 1) in neighbours:
            neighbours.remove((j, 1))
            neighbours.append((j, 2))
        else:
            neighbours.append((j, 1))
        R += Q
    return neighbours


# Finds all isogenous curves to j
# Returns list of tuples (j-invariant, n) where n it the number of edges connecting them
def isogenous_curves_v(j, Phi, l):
    if VELU:
        try:
            return isogenous_curve_velu(EllipticCurve_from_j(j), l)
        except large_extension_error:
            raise
            return
    field = j.parent()
    x = PolynomialRing(field, 'x').gen()
    f = Phi(x, j)
    return f.roots()


# Breadth-first search through the volcano
def BFS(j, l):
    neighbours = {}
    if not VELU:
        Phi = ClassicalModularPolynomialDatabase()[l]
    else:
        Phi = None
    special = False
    vertices = [j]
    queue = [j]
    while queue:

        s = queue.pop(0)

        if s == 0 or s == 1728:
            special = True

        try:
            neighb = isogenous_curves_v(s, Phi, l)
        except large_extension_error:
            raise
            return None, None, None

        neighbours[str(s)] = [s] + neighb
        for i in neighb:
            if not i[0] in vertices:
                queue.append(i[0])
                vertices.append(i[0])

    return neighbours, vertices, special


# Computes volcano depth using number of points on curve
def volcano_depth(l, E=None, D=None):
    if D == None:
        t = E.trace_of_frobenius()
        D = t ** 2 - 4 * E.base_field().order()
    val = ZZ.valuation(l)
    if l == 2 and D.squarefree_part() % 4 != 1:
        D /= 4
    return val(D) // 2


# Function for finding extension of curve E over which the volcano has depth h
# Returns the elliptic curve over the extension
def expand_volcano(E, h, l):
    t = E.trace_of_frobenius()
    p = E.base_field().order()
    D = t ** 2 - 4 * p
    val = ZZ.valuation(l)
    depth = volcano_depth(l, E)
    if depth > 0:

        dif = h - depth
        if dif > 0:
            return extend_field(E, l ** dif)
        else:
            return E
    if l.divides(D):
        D2 = rec_trace(p, l, t) ** 2 - 4 * (p ** l)
        depth = volcano_depth(l, D=D2)

        dif = h - depth

        if dif < 0:

            return extend_field(E, l)
        else:
            return extend_field(E, l * (l ** dif))
    else:
        (a, e1), (b, e2) = eigenvalues(E, l, s=2)
        r = (a * (b ** (-1))).multiplicative_order()
        D2 = rec_trace(p, r, t) ** 2 - 4 * (p ** r)
        depth = volcano_depth(l, D=D2)

        dif = h - depth

        if dif < 0:

            return extend_field(E, r)
        else:
            return extend_field(E, r * (l ** dif))


class Isogeny_graph:

    # Class for construction isogeny graphs with 1 or more degrees
    # ls is a list of primes which define the defining degrees
    def __init__(self, E, ls, special=False):

        self._ls = ls
        j = E.j_invariant()

        self.field = E.base_field()
        self._graph = Graph(multiedges=True, loops=True)

        self._special = False
        self._graph.add_vertex(j)
        queue = [j]
        R = rainbow(len(ls) + 1)
        self._rainbow = R
        self._edge_colors = {R[i]: [] for i in range(len(ls))}

        while queue:
            color = 0
            s = queue.pop(0)

            if s == 0 or s == 1728:
                self._special = True

            for l in ls:
                neighb = isogenous_curves(s, l)

                for i in neighb:
                    if not self._graph.has_vertex(i[0]):
                        queue.append(i[0])
                        self._graph.add_vertex(i[0])
                    if not ((s, i[0], l) in self._edge_colors[R[color]] or (i[0], s, l) in self._edge_colors[R[color]]):
                        for _ in range(i[1]):
                            self._graph.add_edge((s, i[0], l))
                        self._edge_colors[R[color]].append((s, i[0], l))
                color += 1

        if self._special and special:
            print("Curve with j_invariant 0 or 1728 found, may malfunction.")

    def __repr__(self):
        return "Isogeny graph of degrees %r" % (self._ls)

    # Returns degrees of isogenies
    def degrees(self):
        return self._ls

    # Returns list of all edges
    def edges(self):
        return self._graph.edges()

    # Returns list of all vertices
    def vertices(self):
        return self._graph.vertices()

    # Plots the graph
    # Optional arguments figsize, vertex_size, vertex_labels and layout which are the same as in igraph
    def plot(self, figsize=None, edge_labels=False, vertex_size=None, layout=None):
        if vertex_size == None:
            return self._graph.plot(edge_colors=self._edge_colors, figsize=figsize, edge_labels=edge_labels,
                                    layout=layout)
        else:
            return self._graph.plot(edge_colors=self._edge_colors, figsize=figsize, edge_labels=edge_labels,
                                    vertex_size=vertex_size, layout=layout)


class large_extension_error(RuntimeError):
    '''Exception for computation with large extension of base field'''

    def __init__(self, msg):
        self.msg = msg
