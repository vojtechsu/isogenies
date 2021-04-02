# Implementation of Schoof's algorithm from
# https://www.semanticscholar.org/paper/Elliptic-curve-cryptography-Louw/e2e1a03a5682cbe3e401197a20fd64593c1c37cd

from sage.rings.finite_rings.integer_mod import IntegerMod
from sage.rings.all import PolynomialRing, Integer, GF, ZZ
from sage.rings.finite_rings.integer_mod_ring import crt
from sage.rings.all import PolynomialRing
from sage.arith.misc import gcd, power_mod, xgcd, next_prime, CRT_list
from sage.functions.all import sqrt


class EndomorphismMod:
    def __init__(self, E, fx, fy, psi):
        R = E.base_field()['x'].quotient(psi)
        x = R.gen()
        self.E = E
        self.fx = R(fx)
        self.fy = R(fy)
        self.psi = psi
        self.f = x ** 3 + E.a4() * x + E.a6()
        self.A = E.a4()

    def __add__(self, other):
        if isinstance(other, Integer):
            other *= IdentityEndomorphismMod(self.E, self.psi)
        if isinstance(other, ZeroEndomorphismMod):
            return self
        if self.fx == other.fx:
            if self.fy == other.fy:
                m = (3 * self.fx ** 2 + self.A) / (2 * self.fy * self.f)
            else:
                return ZeroEndomorphismMod(self.E, self.psi)

        else:
            div, inv, _ = xgcd(self.fx.parent().lift(self.fx - other.fx), (self.psi))
            if div.is_constant():
                m = (self.fy - other.fy) * inv
            else:
                raise ZeroDivisionError(div)
        fx = m ** 2 * self.f - self.fx - other.fx
        fy = m * (self.fx - fx) - self.fy
        return EndomorphismMod(self.E, fx, fy, self.psi)

    def __radd__(self, other):
        return self + other

    def __neg__(self):
        return EndomorphismMod(self.E, self.fx, -self.fy, self.psi)

    def __sub__(self, other):
        return self + -other

    def __rsub__(self, other):
        return -(self + -other)

    def __mul__(self, other):
        if isinstance(other, Integer) or other == 0:
            if other < 0:
                return -self * -other
            alpha = ZeroEndomorphismMod(self.E, self.psi)
            while other > 0:
                if other % 2 == 1:
                    alpha += self
                self += self
                other //= 2
            return alpha
        try:
            fx = (self.fx.parent().lift(self.fx))(other.fx)
            fy = (self.fx.parent().lift(self.fy))(other.fx) * other.fy
        except AttributeError:
            fx = self.fx(other.fx)
            fy = self.fy(other.fx) * other.fy
        return EndomorphismMod(self.E, fx, fy, self.psi)

    def __rmul__(self, other):
        return self * other

    def __pow__(self, n):
        alpha = IdentityEndomorphismMod(self.E, self.psi)
        while n > 0:
            if n % 2 == 1:
                alpha *= self
            self *= self
            n //= 2
        return alpha

    def __eq__(self, other):
        if isinstance(other, Integer) or other == 0:
            other *= IdentityEndomorphismMod(self.E, self.psi)
        if isinstance(other, ZeroEndomorphismMod):
            return False
        return self.fx == other.fx and self.fy == other.fy


class ZeroEndomorphismMod(EndomorphismMod):
    def __init__(self, E, psi):
        self.E = E
        self.psi = psi

    def __neg__(self):
        return self

    def __add__(self, other):
        return other

    def __mul__(self, other):
        return self

    def __eq__(self, other):
        if isinstance(other, Integer):
            other *= EndomorphismMod(self.E, x, 1, self.psi)
        return isinstance(other, ZeroEndomorphismMod)


class IdentityEndomorphismMod(EndomorphismMod):
    def __init__(self, E, psi):
        x = (E.base_field()['x'].quotient(psi)).gen()
        EndomorphismMod.__init__(self, E, x, 1, psi)


class FrobeniusEndomorphismMod(EndomorphismMod):
    def __init__(self, E, psi):
        q = E.base_field().order()
        x = (E.base_field()['x'].quotient(psi)).gen()
        f = x ** 3 + E.a4() * x + E.a6()
        EndomorphismMod.__init__(self, E, x ** q, f ** ((q - 1) // 2), psi)


def trace_of_frobenius_mod(E, l, candidates=None):
    psi_l = E.division_polynomial(l)
    q_l = E.base_field().order() % l
    t_l = 0
    while True:
        try:
            phi = FrobeniusEndomorphismMod(E, psi_l)

            lhs = phi ** 2 + q_l
            if candidates == None:
                rhs = t_l * phi
                while t_l <= (l - 1) // 2:
                    if lhs == rhs:
                        return t_l
                    elif lhs == -rhs:
                        return -t_l
                    t_l += 1
                    rhs += phi
            else:

                for c in candidates:
                    rhs = c * phi
                    if lhs == rhs:
                        return c
                    elif lhs == -rhs:
                        return -c

        except ZeroDivisionError as e:
            psi_l = e.args[0]


def trace_of_frobenius_mod_2(E):
    F = E.base_field()
    x = PolynomialRing(F, 'x').gen()
    f = x ** 3 + E.a4() * x + E.a6()
    q = F.order()
    if gcd(f, power_mod(x, q, f) - x).is_constant():
        return 1
    else:
        return 0


def prod(A):
    p = 1
    for a in A:
        p *= a
    return p


def schoof(E, info=False):
    q = E.base_field().order()
    residues = [trace_of_frobenius_mod_2(E)]
    moduli = [2]
    l = 3
    while prod(moduli) <= 4 * sqrt(q):
        if q % l == 0:
            l = next_prime(l)
        residues.append(trace_of_frobenius_mod(E, l))
        moduli.append(l)
        l = next_prime(l)
    t = CRT_list(residues, moduli)
    if t > 2 * sqrt(q):
        t = t - prod(moduli)
    if info:
        return t, moduli
    return t
