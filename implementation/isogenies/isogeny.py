from isogenies.utils import *
from isogenies.standard_form import standard_form, normalize_map
from isogenies.velu import *
import copy
from sage.rings.algebraic_closure_finite_field import AlgebraicClosureFiniteField
from sage.arith.misc import factor


class Isogeny:

    # Class for isogenies over finite fields
    # We can construct Isogeny using one of:
    # 1. kernel_polynomial
    # 2. kernel (list of points)
    # 3. rational maps+codomain
    # 4. domain+codomain(only for cyclic,normalized isogenies)
    # 5. isogeny instance of Isogeny class in sage

    # This resulting isogeny and codomain is unique up to isomorphism.
    # The isomorphism can be added by specifiyng the codomain curve
    # We can specify inseparable degree with frobenius power

    def __init__(self, domain, kernel_polynomial=None, frobenius_power=0, kernel=None, codomain=None, isogeny=None,
                 rational_maps=None, degree=None):

        self._domain = domain
        p = domain.base_field().characteristic()
        self._isogeny = isogeny
        self._kernel_polynomial = kernel_polynomial
        self._kernel = kernel
        self._r_frobenius = None
        self._separable_domain = None
        self._separable = None
        self._inseparable_degree = p ** frobenius_power
        self._extended_curve = domain
        self._separable_domain_extended = None
        self._separable_kernel = None
        self._degree = None
        self._separable_composition = None
        self._composition = None
        self._isogeny_factors = None
        self._isomorphism = None
        self._codomain = None
        self._zero = False

        # Dealing with zero isogeny
        if kernel_polynomial == 0 or rational_maps == (0, 0) or rational_maps == 0:
            self._zero = True
            self._degree = 0
            self._codomain = domain if codomain == None else codomain
            return

        # Preparing the inseparable part if needed
        if self._inseparable_degree != 1:
            self._r_frobenius, self._separable_domain = r_frobenius_morphism(domain, frobenius_power)
            self._separable = False

        else:
            self._separable_domain = domain
            self._separable = True

        # Case 1: Creating isogeny using kernel polynomial
        if self._kernel_polynomial != None:
            try:
                self._isogeny = self._domain.isogeny(self._kernel_polynomial)
                # We proceed with Case 5

            except:
                self._kernel, self._extended_curve = kernel_set(domain, self._kernel_polynomial)
                # We proceed with Case 2

        # Case 2: Creating isogeny using kernel
        if self._kernel != None:
            try:
                self._kernel.remove(self._kernel[0].curve()(0))
            except:
                pass
            if self._kernel == []:
                R = PolynomialRing(domain.base_field(), ['x', 'y'])
                x, y = R.gens()
                self._kernel_polynomial = R(1)
                self._codomain = domain
                self._degree = self._inseparable_degree
                self._composition = (x, y)
                self._separable_composition = (x, y)
                computed_codomain = domain
                self._isogeny_factors = None
                self._extended_curve = domain
            else:

                if len(self._kernel) == 1:
                    P = self._kernel[0]
                    self._extended_curve = P.curve()
                    self._kernel = []
                    Q = P
                    while Q != self._extended_curve(0, 1, 0):
                        self._kernel.append(Q)
                        Q += P
                else:

                    self._extended_curve = self._kernel[0].curve()

                try:
                    self._isogeny = self._domain.isogeny(self._kernel)
                    # We proceed with Case 5

                except:

                    try:
                        if self._kernel_polynomial == None:
                            self._kernel_polynomial = kernel_polynomial_from_kernel(self._domain, self._kernel)

                        if self._inseparable_degree != 1:
                            self._separable_domain_extended = self._separable_domain.change_field(
                                self._extended_curve.base_field())
                            self._separable_kernel = map_points(self._r_frobenius, self._kernel,
                                                                self._separable_domain_extended)

                        else:
                            self._separable_domain_extended = self._extended_curve
                            self._separable_kernel = self._kernel

                        self._degree = (len(self._kernel) + 1) * self._inseparable_degree

                        computed_codomain, self._separable_composition = velu(self._separable_kernel,
                                                                              domain=self._separable_domain)
                    except ValueError:
                        raise NoIsogeny("Isogeny doesn't exist")

        # Case 3: Creating isogeny using rational maps and codomain
        if rational_maps != None:
            self._composition = rational_maps

            self._kernel_polynomial = kernel_polynomial_from_maps(self._domain, rational_maps)
            self._codomain = codomain
            self._degree = degree_from_maps(self._domain, rational_maps)
            self._separable_composition, r = extract_frobenius(self._domain, rational_maps)
            self._inseparable_degree = p ** r
            self._separable_domain = frobenius_image_curve(self._domain, r)
            self._separable = self._degree % p != 0
            computed_codomain = codomain
            self._isogeny_factors = None
            self._extended_curve = self._domain

        # Case 4: Creating isogeny using codomain and degree
        if codomain != None and degree != None:
            self._isogeny = self._domain.isogeny(None, codomain=codomain, degree=degree)
            # we proceed with case 5

        # Case 5: Creating isogeny using isogeny implementation
        if self._isogeny != None:
            self._kernel_polynomial = self._isogeny.kernel_polynomial()
            self._codomain = self._isogeny.codomain()
            self._degree = self._isogeny.degree() * self._inseparable_degree
            self._composition = normalize_map(self._isogeny.rational_maps(), self._domain)
            self._separable_composition = self._composition
            computed_codomain = self._isogeny.codomain()
            self._isogeny_factors = None
            self._extended_curve = self._domain

        # Deals with isomorphism if needed
        self._isomorphism = None
        if codomain != None and codomain != computed_codomain:
            self._isomorphism = isomorphism_isogeny(codomain, computed_codomain)

        if rational_maps == None:
            self.compose()

        # Set codomain
        if self._isomorphism == None:
            self._codomain = computed_codomain
        else:
            self._codomain = codomain

    def __repr__(self):

        if self._degree == 0:
            return 'Zero isogeny from %r to %r' % (self._domain, self._codomain)

        return 'Isogeny of degree %r from %r to %r' % (self._degree, self._domain, self._codomain)

    # For internal use only
    # Factors self into a sequence of prime isogenies
    def generate_isogenies(self):
        if self._inseparable_degree != 1:

            current_curve = self._separable_domain_extended
            current_kernel = self._separable_kernel
        else:

            current_curve = self.extended_curve()
            current_kernel = self._kernel

        degree_factors = list(factor(self._degree))

        primes = [i[0] for i in degree_factors for _ in range(i[1])]
        isogenies = list()
        for l in primes:

            isogeny = prime_isogeny(current_curve, current_kernel, l)

            if isinstance(isogeny, tuple):
                current_curve = isogeny[0]
                current_kernel = map_points(isogeny, current_kernel)
            else:
                current_curve = isogeny.codomain()
                current_kernel = map_points(isogeny, current_kernel)
            isogenies.append(isogeny)
        self._isogeny_factors = isogenies

    # Composes the inseparable part, separable part and isomorphism, resulting in the rational maps of self
    def compose(self):

        x, y = PolynomialRing(self._extended_curve.base_ring(), ['x', 'y']).gens()

        if self._inseparable_degree != 1:
            f = self._r_frobenius
        else:
            f = (x, y)

        f = self._separable_composition[0](f[0], f[1]), self._separable_composition[1](f[0], f[1])
        if not self._isomorphism == None:
            f = (self._isomorphism[0](f[0], f[1]), self._isomorphism[1](f[0], f[1]))

        self._composition = standard_form(f, self._domain)

    # Returns kernel as a list of points
    def kernel(self):
        if self.is_zero():
            return None
        if self._kernel != None:
            try:
                return self._kernel + [self._kernel[0].curve()(0)]
            except:
                return self._kernel + [domain(0)]
        self._kernel, self._extended_curve = kernel_set(self._domain, self._kernel_polynomial)
        return self._kernel + [self._kernel[0].curve()(0)]

    # Returns the domain defined over extension over which kernel points are defined
    def extended_curve(self):
        if self.is_zero():
            return None
        if self._kernel != None:
            return self._extended_curve
        self._kernel, self._extended_curve = kernel_set(self._domain, self._kernel_polynomial)
        return self._extended_curve

    # Returns domain of self
    def domain(self):
        return self._domain

    # Returns domain of separable part
    def separable_domain(self):
        return self._separable_domain

    # Returns True if separable or False otherwise
    def separable(self):
        return self._separable

    # Returns codomain of self
    def codomain(self):
        return self._codomain

    # Factorizes the isogeny into a sequence of prime isogenies
    def isogeny_factors(self):
        if self.is_zero():
            return None
        if self._isogeny_factors == None:
            self.generate_isogenies()
        return self._isogeny_factors

    # Returns rational maps of separable part of self, where self = iso*separable_part*(\pi**r)
    def separable_part(self):
        return self._separable_composition

    # Returns the kernel polynomial of self
    def kernel_polynomial(self):
        return self._kernel_polynomial

    # Returns rational maps of self
    def rational_maps(self):
        return self._composition

    # Returns degree of self
    def degree(self):
        return self._degree

    # Returns degree of inseparable part, i.e. p**r where that self = separable_part*(\pi**r)
    def inseparable_degree(self):
        return self._inseparable_degree

    # Defines multiplication of isogenies as composition
    def __mul__(self, other):
        if self.is_zero() or other.is_zero():
            return Isogeny(self.domain(), 0, codomain=self.codomain())

        f = self.rational_maps()
        g = other.rational_maps()
        E = other._domain

        comp = (f[0](g[0], g[1]), f[1](g[0], g[1]))
        return Isogeny(E, rational_maps=standard_form(comp, E), codomain=self.codomain())

    # Opposite composition
    def __rmul__(self, other):
        if self.is_zero() or other.is_zero():
            return Isogeny(self.domain(), 0, codomain=other.codomain())

        f = self.rational_maps()
        g = other.rational_maps()

        comp = (g[0](f[0], f[1]), g[1](f[0], f[1]))
        return Isogeny(self._domain, rational_maps=standard_form(comp, self._domain), codomain=other.codomain())

    # Defines addition of isogenies with the same domain and codomain
    def __add__(self, other):
        if self.is_zero():
            return other
        if other.is_zero():
            return self

        f = self.rational_maps()
        g = other.rational_maps()
        sum = add_maps(f, g, self.domain())

        return Isogeny(self.domain(), rational_maps=sum, codomain=self.codomain())

    # Addition of isogenies is commutative
    def __radd__(self, other):
        return __add__(self, other)

    # Switches sign of self, i.e. self<- (-1)*self
    def switch_sign(self):
        if not self.is_zero():
            self._composition = (self._composition[0], -self._composition[1])

    # Returns (-1)*self
    def __neg__(self):
        I = copy.deepcopy(self)
        I.switch_sign()
        return I

    # Defines substraction using addition
    def __sub__(self, other):

        return self.__add__(other.__neg__())

    def __rsub__(self, other):
        return (self.__sub__(other)).__neg__()

    # We can change the codomain (which must be isomorphic to current codomain)
    def change_codomain(self, iso_codomain):
        if self.is_zero():
            codomain = iso_codomain

        iso = isomorphism_isogeny(self._codomain, iso_codomain)

        try:
            self._isogeny.set_post_isomorphism(self._codomain.isomorphism_to(iso_codomain))
            self._separable_composition = self._isogeny.rational_maps()
            self._composition = self._isogeny.rational_maps()

        except:
            self._composition = iso[0](self._composition[0], self._composition[1]), iso[1](self._composition[0],
                                                                                           self._composition[1])

            self._separable_composition = iso[0](self._separable_composition[0], self._separable_composition[1]), iso[
                1](self._separable_composition[0], self._separable_composition[1])

        if self._isomorphism != None:
            self._isomorphism = iso[0](self._isomorphism[0], self._isomorphism[1]), iso[1](self._isomorphism[0],
                                                                                           self._isomorphism[1])
        else:
            self._isomorphism = iso
        self._codomain = iso_codomain

    # Returns iso where self = pi**r*separable_part*iso
    def isomorphism(self):
        return self._isomorphism

    # Returns true if self is zero isogeny and false otherwise
    def is_zero(self):
        return self._zero

    # Defines equality of isogenies using kernel polynomial, degree, codomain, domain and rational maps
    def __eq__(self, other):
        ker_poly = self.kernel_polynomial() == other.kernel_polynomial()
        deg = self.degree() == other.degree()
        codomain = self.codomain() == other.codomain()
        domain = self.domain() == other.domain()
        maps = self.rational_maps() == other.rational_maps()
        return ker_poly and deg and codomain and domain and maps

    # Computes dual isogeny
    # Implemented only for separable isogenies
    def dual(self):
        if self._isogeny != None:
            try:
                I = Isogeny(self.codomain(),isogeny = self._isogeny.dual(), codomain = self.domain())
                if (I*self).rational_maps()== self.domain().multiplication_by_m(I.degree()):
                    return I
                else:
                    return -I
            except:
                pass

        if self._inseparable_degree != 1:
            raise NotImplementedError("Dual isogeny is implemented only for separable isogenies")

        if len(self._kernel) < 2:
            return copy.deepcopy(self)

        tor, ext = torsion_set(self._domain, self.degree())
        f, g = self.rational_maps()
        cod_ext = self.codomain().change_ring(ext.base_field())
        kernel = []
        for P in tor:
            try:
                Q = cod_ext(f(P[0], P[1]), g(P[0], P[1]))
                kernel.append(Q)
            except:
                continue
        kernel = list(dict.fromkeys(kernel))
        I = Isogeny(self.codomain(), kernel=kernel, codomain=self.domain())
        if (I*self).rational_maps()== self.domain().multiplication_by_m(I.degree()):
            return I
        else:
            return -I

    # Defines mapping of point
    def __call__(self, P):
        f, g = self.rational_maps()
        cod = self.codomain()
        try:
            return cod(f(P[0], P[1]), g(P[0], P[1]))
        except:
            return cod(0)


# Some usefull functions used in Isogeny class

# Maps all points in 'kernel' with the 'isogeny' (Isogeny object or tupleof rational_maps with specified codomain)
# and returns a set of images
def map_points(isogeny, kernel, codomain=None):
    if isinstance(isogeny, tuple):
        f, g = isogeny
    else:
        f, g = isogeny.rational_maps()
        codomain = isogeny.codomain()
    image = list()
    for P in kernel:
        if f.denominator()(P[0], P[1]) == 0:
            continue
        x = f(P[0], P[1])
        y = g(P[0], P[1])
        image.append(codomain(x, y))
    return image


# Finds a point of order l in points or None
def l_point(points, l):
    E = points[0].curve()
    for P in points:
        if l * P == E(0, 1, 0) and P != E(0, 1, 0):
            return P
    return None


# Generates an isogeny of prime degree l from (either instance of sage Isogeny class) or
# rational maps computed using Velu algorithm
def prime_isogeny(E, kernel, l):
    gen = l_point(kernel, l)
    try:
        return E.isogeny(gen)
    except:

        return velu([gen], domain=E)


class NoIsogeny(ValueError):
    '''Isogeny doesn't exist'''
    pass
