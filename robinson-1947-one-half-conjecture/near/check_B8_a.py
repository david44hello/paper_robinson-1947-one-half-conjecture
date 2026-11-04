#!/usr/bin/env python3
"""Robinson 1947, program a: independent exact B8 audit, no program-b code.
Version 0.10 — 20261101__23:16 ET. Tensor polynomial and closed rational q-cell completion, including the exact e vertex.
"""
import argparse
from fractions import Fraction as F
import json
import sympy as sp
from derive_model_area_low import derive_coefficients
from check_model_area_envelope import circle_norm
from check_pureA_coercivity import bernstein2
from check_EUC_B5_area import sqrt_upper, gamma_upper, model_caps
from check_B7R_a import operators, resummed_value_derivative


def model_certificate():
    tt, cc, xx = sp.symbols('t c x')
    vv, ss, dd = 1 - tt**2, sp.Rational(1, 4) - tt**2, cc - tt
    nlocal = vv * (6 * dd**2 + 8 * tt * dd) - 4 * tt * dd**3 - 6 * tt**2 * dd**2
    numerator = sp.Poly(vv * (2 * (1 - 2 * tt * cc) * vv**2 - ss * nlocal), cc)
    denominator = sp.Poly((vv**2 + dd**2 * ss) * (vv**2 - (cc**2 - tt**2) * ss), cc)
    ncoef = [sp.Poly(numerator.nth(index), tt, xx, domain=sp.QQ) for index in range(numerator.degree() + 1)]
    dcoef = [sp.Poly(denominator.nth(index), tt, xx, domain=sp.QQ) for index in range(denominator.degree() + 1)]
    cheb = [sp.Poly(sp.chebyshevt(index, xx), tt, xx, domain=sp.QQ) for index in range(5)]
    real_num = sp.Poly(0, tt, xx, domain=sp.QQ)
    for index, first in enumerate(ncoef):
        for other, second in enumerate(dcoef):
            real_num += first * second * cheb[abs(index - other)]
    den_square = circle_norm(denominator.as_expr(), tt, cc, xx)
    qnum, qden = sp.Rational(1, 2) - tt, sp.Rational(3, 4) * (sp.Rational(5, 4) + 2 * tt)
    difference = sp.Poly(qden, tt, xx) * real_num - sp.Poly(qnum, tt, xx) * den_square
    divided, remainder = sp.div(sp.Poly(difference.as_expr(), xx), sp.Poly(1 - xx, xx))
    assert remainder.is_zero
    target = sp.Poly(divided.as_expr(), tt, xx) - sp.Poly((sp.Rational(109, 50) + sp.Rational(21, 50) * xx) * qden, tt, xx) * den_square
    minimum, degrees, count = bernstein2(target, (tt, xx), [(F(9, 20), F(1, 2)), (F(-1), F(1))])
    assert minimum > 0
    print('MODEL exact tensor min', minimum, 'degrees/count', degrees, count, flush=True)
    return str(minimum)


def finite_norm_certificate():
    base, tf, cf, coefficients = derive_coefficients()
    tt, cc, xx = sp.symbols('t c x')
    common = base(coefficients[-1].denom)
    vf, sf, df = 1 - tf**2, base(1) / 4 - tf**2, cf - tf
    model_denominator = (vf**2 + df**2 * sf) * (vf**2 - (cf**2 - tf**2) * sf)
    ratio = common / model_denominator**2
    assert ratio.numer.degrees()[1] == 0 and ratio.denom.degrees()[1] == 0
    for expression in [ratio.numer.as_expr(), ratio.denom.as_expr()]:
        polynomial = sp.Poly(expression, tt, domain=sp.QQ)
        assert polynomial.eval(sp.Rational(9, 20)) != 0 and polynomial.eval(sp.Rational(1, 2)) != 0
        assert polynomial.count_roots(sp.Rational(9, 20), sp.Rational(1, 2)) == 0
    den_square = circle_norm(common.as_expr(), tt, cc, xx)
    weighted = sp.Poly(0, tt, xx, domain=sp.QQ)
    for index, coefficient in enumerate(coefficients, 2):
        numerator = coefficient * common
        assert all(degree == 0 for degree in numerator.denom.degrees())
        weighted += circle_norm(numerator.as_expr(), tt, cc, xx).mul_ground(sp.Rational(1, 2 * index - 1))
    target = sp.Poly(20 + 260 * (1 - xx), tt, xx) * den_square - weighted
    minimum, degrees, count = bernstein2(target, (tt, xx), [(F(9, 20), F(1, 2)), (F(-1), F(1))])
    assert minimum > 0
    print('NORM exact tensor min', minimum, 'degrees/count', degrees, count, flush=True)
    return str(minimum)


def tail_and_model_h(radius, kappa):
    def value_derivative(point):
        value = F(20, 33) * F(4, 3)**6 * point**7 / ((1 - F(2, 3) * point)**3 * (1 - 2 * point) * (1 - kappa * point)**3)
        derivative = value * (7 / point + 2 / (1 - F(2, 3) * point) + 2 / (1 - 2 * point) + 3 * kappa / (1 - kappa * point))
        return value, derivative
    hh, ww = operators(radius, value_derivative)
    size = radius**2
    tcap, _ = model_caps(kappa, size)
    lcap = min(F(20, 9), kappa**2 + F(4, 3) * kappa)
    model_h = (1 - lcap * size) / (1 + kappa**2 * size)**2
    assert model_h > 0
    return (ww + tcap * hh) / model_h, model_h


def quadratic_minimum(c0, linear, norm, high, end):
    affine_min = min(c0, c0 + linear * end)
    assert affine_min > 0
    p0, p1, p2 = c0**2, 2 * c0 * linear - norm * high, linear**2 - 130 * high
    minimum = min(p0, p0 + p1 * end + p2 * end**2)
    if p2 > 0 and p1 < 0 and -p1 < 2 * p2 * end:
        minimum = min(minimum, p0 - p1**2 / (4 * p2))
    assert minimum > 0
    return affine_min, minimum


def cell_certificate(low, high, radius):
    size = radius**2
    gamma = min(F(1), gamma_upper(low, high))
    kappa = min(F(2), sqrt_upper(F(16, 9) * (F(11, 20)**2 + 4 * (1 - low) * (F(1, 2) - low)))) if low < F(1, 2) else F(7, 10)
    tail, model_h = tail_and_model_h(radius, kappa)
    norm = 20 + tail**2
    hz, _ = operators(radius, lambda point: resummed_value_derivative(point, kappa, gamma, False))
    hr, wr = operators(radius, lambda point: resummed_value_derivative(point, kappa, gamma, True))
    universal = F(16, 3) * size / (1 - 4 * size)**2 + 4 * size / (1 - 4 * size)
    actual_h = max(1 - universal, model_h - gamma * hz)
    assert actual_h > 0
    tcap, _ = model_caps(kappa, size)
    norm_upper = sqrt_upper(norm + 520 * (1 - low))
    remainder = (wr + tcap * hr + norm_upper * hz) / actual_h
    linear = (F(22, 25) + F(21, 100) * low) / size - high * remainder
    return quadratic_minimum(F(16, 27) - F(1, 20), linear, norm, high, 4 * (1 - low))


def run_certificate(radius, cells):
    assert F(1, 4) - radius**2 >= F(9, 20)**2
    assert 4 * (F(1, 4) - F(9, 20)**2) < 1
    assert F(20, 9) * (F(1, 4) - F(9, 20)**2) < 1
    model_min, norm_min = model_certificate(), finite_norm_certificate()
    rows = [(cell_certificate(F(index, cells), F(index + 1, cells), radius), index) for index in range(cells)]
    affine, affine_index = min((result[0], index) for result, index in rows)
    quadratic, quadratic_index = min((result[1], index) for result, index in rows)
    print(json.dumps({'status': 'INDEPENDENT EXACT PASS', 'radius': str(radius), 'cells': cells, 'model_Bernstein_min': model_min, 'norm_Bernstein_min': norm_min,
                      'min_affine_decimal': float(affine), 'min_affine_cell': affine_index, 'min_quadratic_decimal': float(quadratic), 'min_quadratic_cell': quadratic_index,
                      'min_affine_exact': str(affine), 'min_quadratic_exact': str(quadratic), 'method': 'whole rational functions at +/-R, exact e-vertex; no author code or truncation'}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', required=True, action='store_true')
    parser.add_argument('--radius', required=True, type=F)
    parser.add_argument('--cells', required=True, type=int)
    args = parser.parse_args()
    run_certificate(args.radius, args.cells)
