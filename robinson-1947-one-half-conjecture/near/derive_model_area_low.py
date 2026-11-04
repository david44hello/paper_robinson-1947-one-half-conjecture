#!/usr/bin/env python3
"""Robinson 1947, program a: exact full-model area derivatives in Q(t,c).
Version 0.10 — 20261101__22:02 ET. Algebraic reduction only, not a norm bound.
"""
import argparse
import sympy as sp
from sympy.polys.fields import field


class Pair:
    """Two coefficients in the quadratic algebra h^2=-s over a rational field."""

    def __init__(self, first, second, relation):
        self.first, self.second, self.relation = first, second, relation

    def convert(self, other):
        return other if isinstance(other, Pair) else Pair(other, 0, self.relation)

    def __add__(self, other):
        other = self.convert(other)
        return Pair(self.first + other.first, self.second + other.second, self.relation)

    __radd__ = __add__

    def __neg__(self):
        return Pair(-self.first, -self.second, self.relation)

    def __sub__(self, other):
        return self + -self.convert(other)

    def __mul__(self, other):
        other = self.convert(other)
        return Pair(self.first * other.first + self.relation * self.second * other.second, self.first * other.second + self.second * other.first, self.relation)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.convert(other)
        den = other.first**2 - self.relation * other.second**2
        return self * Pair(other.first / den, -other.second / den, self.relation)

    def __rtruediv__(self, other):
        return self.convert(other) / self

    def __pow__(self, exponent):
        result = self.convert(1)
        for _ in range(exponent):
            result = result * self
        return result


def derive_coefficients():
    base, tt, cc = field('t,c', sp.QQ)
    ss = base(1) / 4 - tt**2
    vv = 1 - tt**2
    hh = Pair(base.zero, base.one, -ss)
    aa, bb = (cc - tt) / vv, tt / vv
    physical = hh * (1 + bb * hh) / (1 + (-aa) * hh)**2
    ha = (1 - (aa**2 + 2 * bb * aa) * ss) / (1 + aa**2 * ss)**2
    assert physical.second == ha
    dd = 2 * (1 - 2 * tt * cc) / vv
    nn = 6 * aa**2 + 8 * bb * aa - 4 * tt * aa**3 - 6 * tt * bb * aa**2
    quotient = (dd - ss * nn) / ((1 + aa**2 * ss) * (1 - (aa**2 + 2 * bb * aa) * ss))
    output = []
    for index in range(2, 6):
        derivative = -2 * hh**(index + 1) / (vv**index * (1 + (-aa) * hh)**3 * (1 + bb * hh)**(index - 2))
        logarithmic = (index + 1) / hh + (2 - index) * bb / (1 + bb * hh) + 3 * aa / (1 + (-aa) * hh)
        functional = ((hh + (-tt)) * derivative * logarithmic) - derivative * (quotient - 1)
        coefficient = -functional.second / (ha * ss)
        output.append(coefficient)
        print('U', index, 'numerator degree', coefficient.numer.degrees(), 'denominator degree', coefficient.denom.degrees(), 'terms', len(coefficient.numer), len(coefficient.denom), flush=True)
    return base, tt, cc, output


def run_derivation():
    _, tt, cc, output = derive_coefficients()
    expected = 64 * (1 - 2 * tt) * (4 * tt + 1) * (10 * tt + 7) / (9 * (1 - tt**2) * (8 * tt + 5)**2)
    assert output[0].evaluate(cc, 1) == expected.evaluate(cc, 1)
    print('PASS: full-model derivatives reduced; U2 at c=1 agrees with accepted Koebe formula. Uniform norm TARGET not proved.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', required=True, action='store_true')
    parser.parse_args()
    run_derivation()
