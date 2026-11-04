#!/usr/bin/env python3
"""Robinson 1947, program a: quadratic model margin and shared area square.
Version 0.30. Exact quadratic model margin and shared area square.
"""
import argparse
from fractions import Fraction as F
import sympy as sp
from derive_model_area_low import derive_coefficients
from check_model_area_envelope import circle_norm
from check_pureA_coercivity import bernstein2
from check_EUC_B5_area import sqrt_upper, gamma_upper, parity_values, model_caps
from check_EUC_B6 import high_area_tail


def model_margin_certificate():
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
    boundary_margin = sp.Rational(113, 50) + sp.Rational(17, 50) * xx
    target = sp.Poly(divided.as_expr(), tt, xx) - sp.Poly(boundary_margin * qden, tt, xx) * den_square
    minimum, degrees, count = bernstein2(target, (tt, xx), [(F(23, 50), F(1, 2)), (F(-1), F(1))])
    print('quadratic MODEL min', str(minimum), 'decimal', float(minimum), 'degrees/count', degrees, count, flush=True)
    assert minimum > 0


def norm_certificate():
    base, _, _, coefficients = derive_coefficients()
    tt, cc, xx = sp.symbols('t c x')
    common = base(coefficients[-1].denom)
    den_square = circle_norm(common.as_expr(), tt, cc, xx)
    weighted = sp.Poly(0, tt, xx, domain=sp.QQ)
    for index, coefficient in enumerate(coefficients, 2):
        numerator = coefficient * common
        assert all(degree == 0 for degree in numerator.denom.degrees())
        weighted += circle_norm(numerator.as_expr(), tt, cc, xx).mul_ground(sp.Rational(1, 2 * index - 1))
    target = sp.Poly(20 + 260 * (1 - xx), tt, xx) * den_square - weighted
    minimum, degrees, count = bernstein2(target, (tt, xx), [(F(23, 50), F(1, 2)), (F(-1), F(1))])
    print('low area NORM min', str(minimum), 'decimal', float(minimum), 'degrees/count', degrees, count, flush=True)
    assert minimum > 0


def shared_square(point):
    first = F(256, 243) * point**4 / (1 - F(2, 3) * point)**2
    firstp = first * (4 / point + F(4, 3) / (1 - F(2, 3) * point))
    second = F(4096, 3645) * point**5 / ((1 - F(2, 3) * point)**2 * (1 - 2 * point))
    secondp = second * (5 / point + F(4, 3) / (1 - F(2, 3) * point) + 2 / (1 - 2 * point))
    return first + second, firstp + secondp


def remainder_parities(radius, kappa, beta):
    def value_derivative(point):
        budget, budgetp = shared_square(point)
        den = 1 - kappa * point - beta * point**2 / (1 - 2 * point)
        assert den > 0
        denp = -kappa - beta * (2 * point - 2 * point**2) / (1 - 2 * point)**2
        numerator = 3 * point * (1 + F(2, 3) * point) * budget
        numeratorp = 3 * ((1 + F(4, 3) * point) * budget + point * (1 + F(2, 3) * point) * budgetp)
        return numerator / den**4, numeratorp / den**4 - 4 * numerator * denp / den**5
    plus, plusp = value_derivative(radius)
    minus, minusp = value_derivative(-radius)
    return (plus - minus) / 2, (plusp + minusp) / 2, (plusp - minusp) / 2


def quadratic_cell(low, high, radius):
    size = radius**2
    gamma = gamma_upper(low, high)
    kappa = min(F(2), sqrt_upper(F(16, 9) * (F(27, 50)**2 + 4 * (1 - low) * (F(1, 2) - low)))) if low < F(1, 2) else F(7, 10)
    beta = F(16, 15) * gamma
    odd, oddp, evenp = remainder_parities(radius, kappa, beta)
    hr = odd / radius
    ww = (radius * oddp + F(7, 3) * odd) / radius**3 + evenp / (2 * radius**3)
    zo, _, _ = parity_values(radius, kappa, beta, F(0), F(1), 3)
    hz = zo / radius
    tcap, _ = model_caps(kappa, size)
    norm = sqrt_upper(24 + 520 * (1 - low))
    universal = F(16, 3) * size / (1 - 4 * size)**2 + 4 * size / (1 - 4 * size)
    ha = (1 - F(20, 9) * size) / (1 + kappa**2 * size)**2
    hlower = max(1 - universal, ha - gamma * hz)
    assert hlower > 0
    jj = (ww + tcap * hr + norm * hz) / hlower
    lhs = high * jj + sqrt_upper(130 * high) + F(45, 4) * high
    rhs = (F(24, 25) + F(17, 100) * low) / size
    return lhs / rhs


def run_certificate():
    model_margin_certificate()
    norm_certificate()
    radius = F(23, 120)
    assert F(1, 4) - radius**2 > F(23, 50)**2
    tail = F(10, 11) * high_area_tail(radius)
    assert tail < 2
    rows = [(quadratic_cell(F(index, 200), F(index + 1, 200), radius), index) for index in range(200)]
    ratio, index = max(rows)
    print('shared-square completion max ratio', float(ratio), 'cell', index, 'tail norm', float(tail), flush=True)
    assert ratio < F(199, 200) < 1
    assert 24 / (4 * (F(16, 27) - F(1, 20))) < F(45, 4)
    print('PASS: R=23/120, theta <= 2 asin(23/60).', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', required=True, action='store_true')
    parser.parse_args()
    run_certificate()
