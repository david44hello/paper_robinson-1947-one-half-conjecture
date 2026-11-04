#!/usr/bin/env python3
"""Independent exact certificate for program a's 165-degree sector.
Version 0.10 — program b, 20261101__19:52 ET. SymPy polynomial composition, not author's Fraction/de Casteljau implementation.
"""

import argparse
from fractions import Fraction as Q
from math import factorial
import json
import sympy as sp
from AP_check_b import exponential_bounds


def certificate_polynomial(variable):
    polynomial = lambda expression: sp.Poly(expression, variable, domain=sp.QQ)
    denominator = polynomial(1+variable**2)
    cosine = polynomial(sp.Rational(253, 2000)*(1-variable**2)+sp.Rational(59, 50)*variable)
    argument = polynomial(sp.Rational(11, 10)*(1-variable**2)+sp.Rational(1357, 10000)*variable)
    numerator = sp.Rational(26, 25)*denominator-cosine
    exponential = polynomial(0)
    for index in range(9):
        exponential += numerator**index*denominator**(8-index)/factorial(index)
    lower_cosine = denominator**6-argument**2*denominator**4/2
    lower_cosine += argument**4*denominator**2/24-argument**6/720
    return exponential*lower_cosine-denominator**14


def bernstein_minimum(polynomial, degree):
    coefficients = [sum((polynomial.nth(index)*sp.binomial(order, index)/sp.binomial(degree, index)
                         for index in range(order+1)), sp.Rational(0)) for order in range(degree+1)]
    return min(coefficients)


def check_polynomial():
    variable = sp.symbols('t')
    numerator = certificate_polynomial(variable)
    assert numerator.degree() == 28
    left = numerator.compose(sp.Poly(variable/2, variable, domain=sp.QQ))
    right = numerator.compose(sp.Poly((variable+1)/2, variable, domain=sp.QQ))
    minima = [bernstein_minimum(piece, 28) for piece in [left, right]]
    expected = [sp.Rational(24924593391164862173792291358922003855306557895899339033712756999,
                           8322397690134528000000000000000000000000000000000000000000000000000),
                sp.Rational(23885999931413475021358351083261463412708829402516820734220353673,
                            4453022092492800000000000000000000000000000000000000000000000000)]
    assert minima == expected and min(minima) > 0
    return [str(value) for value in minima]


def check_scalar_inputs():
    atan_lower = sum(((-1)**index*Q(1, 2)**(2*index+1)/factorial(2*index+1) for index in range(6)), Q(0))
    assert atan_lower > Q(1159, 2500)
    assert exponential_bounds(Q(2747, 2500), 12)[0] > 3
    assert exponential_bounds(Q(11, 10), 12)[0] > 3
    assert 4*(Q(2747, 5000)**2-Q(1159, 2500)**2) < Q(59, 100)**2
    assert exponential_bounds(Q(53, 250), 12)[0] > Q(58, 47)
    assert Q(53, 1000)/Q(1159, 2500) < Q(23, 200)
    assert Q(253, 2000)+Q(59, 100) < Q(26, 25)
    assert Q(11, 10)**2+Q(1357, 20000)**2 < Q(6, 5)**2
    assert 1-Q(6, 5)**2/2 > 0 and 1-Q(6, 5)**2/30 > 0
    sine_upper = Q(1, 2)-Q(1, 2)**3/6+Q(1, 2)**5/120
    assert Q(26, 25)*sine_upper < Q(1, 2)
    assert exponential_bounds(Q(91, 100), 12)[1] < Q(875, 351)
    assert exponential_bounds(Q(26, 25), 12)[1] < Q(1000, 351)


def check_mixed_inputs():
    upper_v = Q(287683, 1000000)
    lower_log, upper_log = Q(223143, 1000000), Q(223144, 1000000)
    assert exponential_bounds(upper_v, 12)[0] > Q(4, 3)
    assert exponential_bounds(lower_log, 12)[1] < Q(5, 4)
    assert exponential_bounds(upper_log, 12)[0] > Q(5, 4)
    assert upper_v-Q(2, 9) < Q(33, 500)
    delta_u, delta_v = Q(3, 32)*Q(11, 42)**2, Q(33, 1000)*Q(11, 42)**2
    plus = (Q(4, 9)-Q(4, 25)+delta_u)*(upper_v-lower_log+delta_v)
    minus = (Q(4, 9)+Q(4, 25)+delta_u)*(upper_v+upper_log+delta_v)
    assert plus < Q(7, 50)**2 and minus < Q(14, 25)**2
    assert Q(351, 500)-Q(7, 10) == Q(1, 500)


def run_checks():
    check_scalar_inputs()
    check_mixed_inputs()
    print(json.dumps({'status': 'PASS', 'degree': 28,
                      'bernstein_minima': check_polynomial(), 'Q_margin': '1/500'}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.parse_args()
    run_checks()


if __name__ == '__main__':
    main()
