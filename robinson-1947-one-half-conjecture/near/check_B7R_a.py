#!/usr/bin/env python3
"""Robinson 1947, program a: independent exact B7R audit, no program-b code.
Version 0.10 — 20261101__22:55 ET. Complete rational endpoint/derivative functions and256 cells; no truncated tails.
"""
import argparse
from fractions import Fraction as F
import json
from check_EUC_B5_area import sqrt_upper, gamma_upper, model_caps
from check_EUC_B7 import shared_square


def resummed_value_derivative(point, kappa, gamma, remainder):
    aa, aap = 1 - kappa * point, -kappa
    bb = F(16, 15) * point**2 / (1 - 2 * point)
    bbp = F(16, 15) * (2 * point - 2 * point**2) / (1 - 2 * point)**2
    dd, ddp = aa - gamma * bb, aap - gamma * bbp
    assert aa > 0 and dd > 0
    numerator, numeratorp = point * (1 + F(2, 3) * point), 1 + F(4, 3) * point
    if remainder:
        budget, budgetp = shared_square(point)
        factor = 2 / (aa**3 * dd) + 1 / (aa**2 * dd**2)
        factorp = 6 * kappa / (aa**4 * dd) - 2 * ddp / (aa**3 * dd**2) + 2 * kappa / (aa**3 * dd**2) - 2 * ddp / (aa**2 * dd**3)
    else:
        budget, budgetp = bb, bbp
        factor = 1 / (aa**2 * dd) + 1 / (aa * dd**2)
        factorp = 2 * kappa / (aa**3 * dd) - ddp / (aa**2 * dd**2) + kappa / (aa**2 * dd**2) - 2 * ddp / (aa * dd**3)
    return numerator * budget * factor, (numeratorp * budget + numerator * budgetp) * factor + numerator * budget * factorp


def operators(radius, function):
    plus, plusp = function(radius)
    minus, minusp = function(-radius)
    odd, oddp, evenp = (plus - minus) / 2, (plusp + minusp) / 2, (plusp - minusp) / 2
    hh = odd / radius
    ww = (radius * oddp + F(7, 3) * odd) / radius**3 + evenp / (2 * radius**3)
    return hh, ww


def high_tail(radius):
    def value_derivative(point):
        value = F(20, 33) * F(4, 3)**6 * point**7 / ((1 - F(2, 3) * point)**3 * (1 - 2 * point)**4)
        derivative = value * (7 / point + 2 / (1 - F(2, 3) * point) + 8 / (1 - 2 * point))
        return value, derivative
    hh, ww = operators(radius, value_derivative)
    size = radius**2
    tcap, _ = model_caps(F(2), size)
    ha = (1 - F(20, 9) * size) / (1 + 4 * size)**2
    return (ww + tcap * hh) / ha


def completion_cell(low, high, radius):
    size = radius**2
    gamma = min(F(1), gamma_upper(low, high))
    kappa = min(F(2), sqrt_upper(F(16, 9) * (F(27, 50)**2 + 4 * (1 - low) * (F(1, 2) - low)))) if low < F(1, 2) else F(7, 10)
    hz, _ = operators(radius, lambda point: resummed_value_derivative(point, kappa, gamma, False))
    hr, wr = operators(radius, lambda point: resummed_value_derivative(point, kappa, gamma, True))
    universal = F(16, 3) * size / (1 - 4 * size)**2 + 4 * size / (1 - 4 * size)
    ha = (1 - F(20, 9) * size) / (1 + kappa**2 * size)**2
    actual_h = max(1 - universal, ha - gamma * hz)
    assert actual_h > 0
    tcap, _ = model_caps(kappa, size)
    norm = sqrt_upper(F(45, 2) + 520 * (1 - low))
    jj = (wr + tcap * hr + norm * hz) / actual_h
    cost = high * jj + sqrt_upper(130 * high) + F(21, 2) * high
    margin = (F(24, 25) + F(17, 100) * low) / size
    return cost / margin


def run_certificate():
    radius = F(39, 200)
    assert F(1, 4) - radius**2 > F(23, 50)**2
    tail = high_tail(radius)
    assert tail**2 < F(5, 2)
    rows = [(completion_cell(F(index, 256), F(index + 1, 256), radius), index) for index in range(256)]
    ratio, index = max(rows)
    assert ratio < F(199, 200)
    assert F(45, 2) / (4 * (F(16, 27) - F(1, 20))) < F(21, 2)
    print(json.dumps({'status': 'INDEPENDENT EXACT PASS', 'tail_norm_exact': str(tail), 'tail_norm_decimal': float(tail), 'tail_square_decimal': float(tail**2),
                      'cells': 256, 'maximum_ratio_exact': str(ratio), 'maximum_ratio_decimal': float(ratio), 'maximum_cell': index,
                      'method': 'complete rational value and analytic derivative at plus/minus R; no author code and no truncation'}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', required=True, action='store_true')
    parser.parse_args()
    run_certificate()
