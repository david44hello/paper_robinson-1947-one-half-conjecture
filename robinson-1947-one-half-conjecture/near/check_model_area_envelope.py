#!/usr/bin/env python3
"""Module of the second program: finite polynomial model-area norm.
Version 0.30 — 20261101__22:02 ET. Explicit rational polynomial domains; never infer positivity from an uncertified coefficient.
"""
import argparse
from fractions import Fraction as F
import sympy as sp
from derive_model_area_low import derive_coefficients
from check_pureA_coercivity import bernstein2


def circle_norm(polynomial, parameter, model, real_part):
    local = sp.Poly(polynomial, model)
    coefficients = [sp.Poly(local.nth(index), parameter, real_part, domain=sp.QQ) for index in range(local.degree() + 1)]
    chebyshev = [sp.Poly(sp.chebyshevt(index, real_part), parameter, real_part, domain=sp.QQ) for index in range(local.degree() + 1)]
    result = sp.Poly(0, parameter, real_part, domain=sp.QQ)
    for index, coefficient in enumerate(coefficients):
        result += coefficient**2
        for other in range(index):
            result += 2 * coefficient * coefficients[other] * chebyshev[index - other]
    return result


def envelope_polynomial():
    base, tt, cc, coefficients = derive_coefficients()
    parameter, model, real_part = sp.symbols('t c x')
    common = base(coefficients[-1].denom)
    denominator = circle_norm(common.as_expr(), parameter, model, real_part)
    weighted = sp.Poly(0, parameter, real_part, domain=sp.QQ)
    for index, coefficient in enumerate(coefficients, 2):
        numerator = coefficient * common
        assert all(degree == 0 for degree in numerator.denom.degrees())
        weighted += circle_norm(numerator.as_expr(), parameter, model, real_part).mul_ground(sp.Rational(1, 2 * index - 1))
    target = sp.Poly(24 + 300 * (1 - real_part), parameter, real_part) * denominator - weighted
    print('target degrees', target.degree(parameter), target.degree(real_part), 'terms', len(target.terms()), flush=True)
    return target, parameter, real_part


def run_certificate():
    polynomial, parameter, real_part = envelope_polynomial()
    minimum, degrees, count = bernstein2(polynomial, (parameter, real_part), [(F(47, 100), F(1, 2)), (F(-1), F(1))])
    print('single-box Bernstein minimum', minimum, 'decimal', float(minimum), 'degrees/count', degrees, count, flush=True)
    assert minimum > 0, 'No positivity certificate from this single box; not a counterexample.'
    print('PASS: four-coefficient squared norm <=24+150e on c circle; norm subharmonicity extends inside. Tail and nonlinear quotient are checked separately.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', required=True, action='store_true')
    parser.parse_args()
    run_certificate()
