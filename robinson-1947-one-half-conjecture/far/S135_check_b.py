#!/usr/bin/env python3
"""Independent exact interval and polynomial checker for S135.
Version 0.10 — program b, 20261101__20:04 ET. Outward rational grid 1e-12; direct uniform-depth polynomial substitutions, no author code.
"""

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, isqrt
from pathlib import Path
import json
import sympy as sp
from AP_check_b import exponential_bounds
from S165_check_b import bernstein_minimum


def rounded(lower, upper):
    scale = 10**12
    down = lower.numerator*scale//lower.denominator
    up = -((-upper.numerator*scale)//upper.denominator)
    return Interval(Q(down, scale), Q(up, scale))


class Interval:
    def __init__(self, lower, upper=None):
        self.lower = Q(lower)
        self.upper = self.lower if upper is None else Q(upper)
        assert self.lower <= self.upper

    @staticmethod
    def cast(value):
        return value if isinstance(value, Interval) else Interval(value)

    def __add__(self, other):
        other = self.cast(other)
        return rounded(self.lower+other.lower, self.upper+other.upper)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.upper, -self.lower)

    def __sub__(self, other):
        return self+-self.cast(other)

    def __rsub__(self, other):
        return self.cast(other)+-self

    def __mul__(self, other):
        other = self.cast(other)
        products = [first*second for first in [self.lower, self.upper]
                    for second in [other.lower, other.upper]]
        return rounded(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        assert other.lower*other.upper > 0
        return self*rounded(1/other.upper, 1/other.lower)

    def __rtruediv__(self, other):
        return self.cast(other)/self

    def __pow__(self, degree):
        assert isinstance(degree, int) and degree >= 0
        if degree == 0:
            return Interval(1)
        endpoints = [self.lower**degree, self.upper**degree]
        lower = 0 if degree % 2 == 0 and self.lower < 0 < self.upper else min(endpoints)
        return rounded(Q(lower), max(endpoints))


def square_root(interval):
    # All uses are known nonnegative radicands: squared norms or R^2-4|Z|^2.
    assert interval.upper >= 0
    scale = 10**12
    lower, upper = max(Q(0), interval.lower), interval.upper
    low_integer = isqrt(lower.numerator*scale**2//lower.denominator)
    high_integer = isqrt(upper.numerator*scale**2//upper.denominator)+1
    return Interval(Q(low_integer, scale), Q(high_integer, scale))


def atanh_scalar(argument):
    assert 0 <= argument <= Q(1, 2)
    lower = sum((argument**(2*index+1)/Q(2*index+1) for index in range(32)), Q(0))
    return lower, lower+argument**65/(65*(1-argument**2))


def atan_small(argument):
    assert 0 <= argument <= Q(1, 2)
    lower = sum(((-1)**index*argument**(2*index+1)/Q(2*index+1) for index in range(16)), Q(0))
    return lower, lower+argument**33/33


@lru_cache(maxsize=1)
def pi_bounds():
    first, second = atan_small(Q(1, 5)), atan_small(Q(1, 239))
    tangent = (Q(120, 119)-Q(1, 239))/(1+Q(120, 119)*Q(1, 239))
    assert tangent == 1  # Machin's angle is in (0,pi/2), hence exactly pi/4.
    return 16*first[0]-4*second[1], 16*first[1]-4*second[0]


def atan_scalar(argument):
    if argument <= Q(1, 2):
        return atan_small(argument)
    assert 1 <= argument <= Q(3, 2)
    small = atan_small((argument-1)/(argument+1))
    circle = pi_bounds()
    return circle[0]/4+small[0], circle[1]/4+small[1]


def increasing_function(interval, scalar_bounds):
    lower = scalar_bounds(interval.lower)[0]
    upper = scalar_bounds(interval.upper)[1]
    return rounded(lower, upper)


def atanh_interval(interval):
    return increasing_function(interval, atanh_scalar)


def atan_interval(interval):
    return increasing_function(interval, atan_scalar)


def logarithm(interval):
    assert interval.lower >= 1
    return 2*atanh_interval((interval-1)/(interval+1))


def ball_constants(cosine):
    real_part = atanh_interval(Q(4, 5)*cosine)/2
    imaginary_part = atan_interval(Q(4, 3)*square_root(1-cosine**2))/2
    radius = 2*atanh_interval(Interval(Q(1, 2)))
    beta = square_root(radius**2-4*real_part**2)
    first = 4*real_part*imaginary_part/beta
    second = radius*square_root(radius**2-4*real_part**2-4*imaginary_part**2)/beta
    return first, second, beta


def mixed_upper(cosine):
    horizontal = 1-2*cosine**2
    vertical = 2*cosine*square_root(1-cosine**2)
    denominator = 1+Q(1, 2)*horizontal+Q(1, 16)
    first = -Q(1, 4)*(1+Q(1, 2)*horizontal+Q(1, 16)*(2*horizontal**2-1))/denominator**2
    angle = atan_interval(Q(1, 4)*vertical/(1+Q(1, 4)*horizontal))
    second = -horizontal*logarithm(denominator)/2-vertical*angle
    norm = logarithm(Interval(Q(4, 3)))
    plus = square_root((Q(4, 9)+first)*(norm+second))
    minus = square_root((Q(4, 9)-first)*(norm-second))
    return plus.upper+minus.upper


def ball_polynomial(first, second, beta):
    variable = sp.symbols('t')
    polynomial = lambda expression: sp.Poly(expression, variable, domain=sp.QQ)
    denominator = polynomial(1+variable**2)
    numerator = polynomial(sp.Rational(211, 200)*(1+variable**2)
                           -sp.Rational(first)*(1-variable**2)-2*sp.Rational(second)*variable)
    argument = polynomial(sp.Rational(beta)*(1-variable**2))
    exponential = polynomial(0)
    for index in range(9):
        exponential += numerator**index*denominator**(8-index)/factorial(index)
    cosine = denominator**6-argument**2*denominator**4/2
    cosine += argument**4*denominator**2/24-argument**6/720
    return exponential*cosine-denominator**14


def check_cover(cells, endpoint):
    cursor = Q(0)
    for cell in cells:
        lower, upper = map(Q, cell['c'])
        assert lower == cursor and lower < upper
        cursor = upper
    assert cursor == endpoint


def check_ball_cover(cells):
    minima = []
    variable = sp.symbols('t')
    for cell in cells:
        lower, upper = map(Q, cell['c'])
        supplied = list(map(Q, cell['a_b_beta']))
        computed = ball_constants(Interval(lower, upper))
        assert all(value.upper <= claimed for value, claimed in zip(computed, supplied))
        assert supplied[0]+supplied[1] < Q(211, 200) and supplied[2] < Q(6, 5)
        numerator = ball_polynomial(*supplied)
        assert numerator.degree() == 28
        for index in range(8):
            affine = sp.Poly((variable+index)/8, variable, domain=sp.QQ)
            minimum = bernstein_minimum(numerator.compose(affine), 28)
            assert minimum > 0
            minima.append(minimum)
    return str(min(minima))


def check_exponential_disk():
    argument, radius = Q(57, 100), Q(211, 200)
    sine_upper = argument-argument**3/6+argument**5/120
    cosine_lower = 1-argument**2/2+argument**4/24-argument**6/720
    assert radius*sine_upper < argument and cosine_lower > Q(21, 25)
    assert exponential_bounds(radius*Q(21, 25), 12)[1] < Q(672, 277)
    assert exponential_bounds(radius, 12)[1] < Q(800, 277)
    small = Q(11, 28)
    assert small-small**3/6+small**5/120 < Q(383, 1000)
    assert Q(277, 400)-Q(173, 250) == Q(1, 2000)


def run_checks(certificate):
    record = json.loads(certificate.read_text())
    endpoint = Q(383, 1000)
    assert Q(record['c_max']) == endpoint and Q(record['T']) == Q(211, 200)
    check_cover(record['ball_cover'], endpoint)
    check_cover(record['mixed_cover'], endpoint)
    check_exponential_disk()
    mixed = [mixed_upper(Interval(*map(Q, cell['c']))) for cell in record['mixed_cover']]
    assert max(mixed) < Q(173, 250)
    print(json.dumps({'status': 'PASS', 'ball_cells': len(record['ball_cover']),
                      'uniform_polynomial_subcells': 8*len(record['ball_cover']),
                      'mixed_cells': len(mixed), 'mixed_upper': str(max(mixed)),
                      'minimum_bernstein': check_ball_cover(record['ball_cover']),
                      'Q_margin': '1/2000'}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.add_argument('--certificate', type=Path, required=True)
    arguments = parser.parse_args()
    run_checks(arguments.certificate)


if __name__ == '__main__':
    main()
