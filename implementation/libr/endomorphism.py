from libr.isogeny import Isogeny
from libr.endomorphism_ring import Endomorphism_ring
from sage.rings.all import PolynomialRing, NumberField
from libr.standard_form import normalize_map, standard_form
from libr.utils import *


class Endomorphism(Isogeny):

    # Class implementing endomorphisms of elliptic curves over finite fields as a subclass of Isogeny class
    # We can construct endomorphism using one of:
    # 1. kernel polynomial
    # 2. rational maps
    # 3. element of its endomorphism ring

    # inseparable degree can be specified

    # Endomorphism ring can be supplied using 'ring' argument (instance of Endomorphism_ring class),
    # otherwise it will be computed if needed

    # It is therefore recommended to avoid elliptic curves with j-invariant 0 or 1728
    # Supersingular endomorphism ring not implemented!

    def __init__(self, E, kernel=None, rational_maps=None, degree=None, kernel_polynomial=None, frobenius_power=0,
                 element=None, ring=None, isogeny=None):

        self._domain = E
        self._ring = ring
        self._field = NumberField(E.frobenius_polynomial(), 'c')
        self._order_element = element
        if isinstance(element, tuple):
            c = self._field.gen()
            self._order_element = element[0] + element[1] * c
        if isinstance(element, Integer):
            self._order_element = self._field(element)
        self._trace = None

        if isogeny != None:
            Isogeny.__init__(self, E, rational_maps=isogeny.rational_maps(), codomain=E)

        # Construction using provided order element
        if element != None:

            # 0 endomorphism has to be dealt with separately
            if element == 0:

                Isogeny.__init__(self, E, 0)
                self._order_element = element
                self._trace = 0

            else:

                k1 = self._order_element.polynomial()[0]
                k2 = self._order_element.polynomial()[1]
                denom = k2.denominator().lcm(k1.denominator())
                a = k1.numerator() * (denom // k1.denominator())
                b = k2.numerator() * (denom // k2.denominator())

                A = multiplication_end(E, a)
                B = multiplication_end(E, b)
                frob = frobenius(E)

                rational_maps = add_maps(A, compose_endomorphisms(B, frob, E), E)
                if denom == 1:
                    Isogeny.__init__(self, E, rational_maps=rational_maps, codomain=E)
                else:
                    kernel = []
                    isg = Isogeny(E, rational_maps=rational_maps, codomain=E)

                    for P in isg.kernel():

                        Q = denom * P
                        if Q != (Q - Q):
                            kernel.append(Q)

                    kernel = list(dict.fromkeys(kernel))

                    Isogeny.__init__(self, E, kernel=kernel, codomain=E)

        # Otherwise use Isogeny class
        else:
            if degree != None:
                Isogeny.__init__(self, E, degree=degree, codomain=E)
            else:
                Isogeny.__init__(self, E, kernel=kernel, rational_maps=rational_maps,
                                 kernel_polynomial=kernel_polynomial, frobenius_power=frobenius_power, codomain=E)

    def __repr__(self):

        return 'Endomorphism of degree %r on %r' % (self._degree, self._domain)

    # Returns quadratic number field containing the endomorphism ring (NumberField class)
    def field(self):
        return self._field

    # Returns trace of endomorphism
    def trace(self):
        if self._trace == None:
            self._trace = self.trace_end()
        return self._trace

    # Returns element of order (as an element of NumberField class)
    def order_element(self):
        if self._order_element == None:
            self._order_element = self.compute_order_element()
        return self._order_element

    # Computes trace of endomorphism (tuple of rational maps) by formula tr(f)=1+deg(f)-deg(1-f)
    def trace_end(self):
        f = self.rational_maps()
        degree = self.degree()
        x, y = PolynomialRing(self._domain.base_field(), ['x', 'y']).gens()
        one = Endomorphism(self._domain, rational_maps=(x, y))
        d = (one - self).degree()

        return -d + degree + 1

    # Computes an element of Endomorphism ring corresponding to rational_maps using the characteristic polynomial
    def compute_order_element(self):
        if self._ring == None:
            self._ring = Endomorphism_ring(self._domain)

        deg = self.degree()
        trace = self.trace()
        R = PolynomialRing(self._ring.field(), 'x')
        x = R.gen()
        char_poly = x ** 2 - trace * x + deg
        roots = char_poly.roots(R)

        roots = [i[0] for i in roots for _ in range(i[1])]
        a = ZZ(roots[0][0].list()[0])
        b = ZZ(roots[0][0].list()[1])
        basis = self._ring.order().basis()

        A = multiplication_end(self._domain, a)  # Isogeny is given by A+B*frobenius
        B = multiplication_end(self._domain, b)
        frob = frobenius(self._domain)
        if self.rational_maps() == add_maps(A, compose_endomorphisms(B, frob, self._domain), self._domain):
            return self._ring.field()(roots[0])
        else:
            return self._ring.field()(roots[1])

    # Returns the endomorphism ring (class Endomorphism_ring) which is computed if needed
    def ring(self):
        if self._ring == None:
            self._ring = Endomorphism_ring(self._domain)
        return self._ring

    # Defines multiplication (composition) of endomorphisms
    def __mul__(self, other):
        if self.is_zero() or other.is_zero():
            return Endomorphism(self.domain(), 0)

        if self._order_element != None and other._order_element != None:
            return Endomorphism(self._domain, element=self.order_element() * other.order_element(), ring=self._ring)

        f = self.rational_maps()
        g = other.rational_maps()
        E = other._domain

        comp = (f[0](g[0], g[1]), f[1](g[0], g[1]))
        return Endomorphism(self._domain, rational_maps=standard_form(comp, self._domain))

    # Multiplication of endomorphisms is commutative
    def __rmul__(self, other):
        return self.__mul__(self, other)

    # Defines addition of endomorphisms
    def __add__(self, other):
        if self.is_zero():
            return other
        if other.is_zero():
            return self

        if self._order_element != None and other._order_element != None:
            return Endomorphism(self._domain, element=self.order_element() + other.order_element(), ring=self._ring)

        f = self.rational_maps()
        g = other.rational_maps()
        return Endomorphism(self.domain(), rational_maps=add_maps(f, g, self.domain()))

    # Addition of endomorphisms is commutative
    def __radd__(self, other):
        return self.__radd__(self, other)

    # Defines negation of endomorphism
    def __neg__(self):
        if self._order_element != None:
            return Endomorphism(self._domain, element=-self.order_element(), ring=self._ring)
        return Isogeny.__neg__(self)

    # Defines substraction of endomorphisms
    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return other - self

    # Returns dual endomorphism of endomorphism
    def dual(self):
        trace = self.trace()
        ring = self.ring()

        t_e = Endomorphism(self._domain, element=ring.field()(trace), ring=ring)

        return t_e - self


# Composes two rational maps(endomorphisms) on E
def compose_endomorphisms(f, g, E):
    if f == 0 or g == 0:
        return 0
    return standard_form((f[0](g[0], g[1]), f[1](g[0], g[1])), E)


# Completing the already implemented multiplication_by_m function, which doesn't work for p|m
def multiplication_end(E, m):
    p = E.base_ring().characteristic()
    Q = PolynomialRing(E.base_field(), ['x', 'y'])
    x, y = Q.gens()
    R = Q.fraction_field()
    if m % p == 0:
        return add_maps(E.multiplication_by_m(m - 1), (R(x), R(y)), E)
    else:
        return normalize_map(E.multiplication_by_m(m), E)
