from isogenies.volcano_depth import find_descending_path
from sage.rings.all import NumberField, GF
from sage.arith.misc import factor
from sage.databases.db_modular_polynomials import ClassicalModularPolynomialDatabase


# Class implementing endomorphism ring of elliptic curves over finite fields
# Computation is done using the isogeny volcanoes (libr.volcano_depth)
class Endomorphism_ring:

    def __init__(self, E):
        self._domain = E
        self._j_invariant = E.j_invariant()
        self._trace = None
        self._order = None
        self._index = None
        self._field = None
        self.endomorphism_ring()

    def __repr__(self):
        return "Endomorphism ring of %r" % self._domain

    # Internal use only
    def endomorphism_index(self):
        j = self._j_invariant
        field = j.parent()
        t = self._domain.trace_of_frobenius()
        self._trace = t
        Dv = t ** 2 - 4 * self._domain.base_field().order()
        D = Dv.squarefree_part()
        v = Dv // D
        if D % 4 != 1:
            v = v // 4
        ls = [(i[0], i[1] // 2) for i in list(factor(v)) if i[1] >= 2]
        u = 1
        for a in ls:
            l = a[0]
            Phi = ClassicalModularPolynomialDatabase()[l]
            dist = len(find_descending_path(j, Phi, l, special=False)) - 1
            ex = a[1] - dist
            u *= l ** ex
        self._index = u

    # Internal use only
    def endomorphism_ring(self):
        k = NumberField(self._domain.frobenius().minpoly(), 'c')
        self._field = k
        self.endomorphism_index()
        basis = k.maximal_order().basis()
        basis = [basis[0] * self._index, basis[1] * self._index]
        self._order = k.order(basis)

    # Returns the imaginary quadratic field
    def field(self):
        return self._field

    # Returns an instance of sage class Order
    def order(self):
        return self._order

    # Returns the conductor of endomorphism ring
    def conductor(self):
        return self._index
