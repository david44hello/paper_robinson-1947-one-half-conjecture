#!/usr/bin/env python3
"""Module of the second program: exact model-area quadratic remainder.
Version 0.20. Exact rational arithmetic.
"""
import argparse
from fractions import Fraction as F
import check_pureA_coercivity as model_certificate
from check_EUC_B5_area import sqrt_upper, gamma_upper, parity_values, model_caps


def model_extension():
    original = model_certificate.bernstein2
    def extended_bounds(poly, variables, bounds):
        return original(poly, variables, [(F(47, 100), F(1, 2)), bounds[1]])
    model_certificate.bernstein2 = extended_bounds
    model_certificate.run_probe(F(2))
    model_certificate.bernstein2 = original
    print('The preceding model polynomial was certified on47/100<=t<=1/2 (the imported legacy PASS text states its older interval).', flush=True)


def high_area_tail(radius):
    def value_derivative(point):
        value = 2 * F(4, 3)**6 / 3 * point**7 * (1 + F(2, 3) * point) / ((1 - F(2, 3) * point)**4 * (1 - 2 * point)**4)
        derivative = value * (7 / point + F(2, 3) / (1 + F(2, 3) * point) + F(8, 3) / (1 - F(2, 3) * point) + 8 / (1 - 2 * point))
        return value, derivative
    plus, plusp = value_derivative(radius)
    minus, minusp = value_derivative(-radius)
    odd, oddp, evenp = (plus - minus) / 2, (plusp + minusp) / 2, (plusp - minusp) / 2
    hh = odd / radius
    ww = (radius * oddp + F(7, 3) * odd) / radius**3 + evenp / (2 * radius**3)
    size = radius**2
    tcap, _ = model_caps(F(2), size)
    ha = (1 - F(20, 9) * size) / (1 + 4 * size)**2
    return (ww + tcap * hh) / ha


def quadratic_cell(low, high, radius):
    size = radius**2
    gamma = gamma_upper(low, high)
    kappa = min(F(2), sqrt_upper(F(16, 9) * (F(53, 100)**2 + 4 * (1 - low) * (F(1, 2) - low)))) if low < F(1, 2) else F(7, 10)
    beta = F(16, 15) * gamma
    odd, oddp, evenp = parity_values(radius, kappa, beta, F(0), F(1), 4)
    hr = odd / radius
    ww = (radius * oddp + F(7, 3) * odd) / radius**3 + evenp / (2 * radius**3)
    zo, _, _ = parity_values(radius, kappa, beta, F(0), F(1), 3)
    hz = zo / radius
    tcap, _ = model_caps(kappa, size)
    norm = sqrt_upper(25 + 600 * (1 - low))
    universal = F(16, 3) * size / (1 - 4 * size)**2 + 4 * size / (1 - 4 * size)
    jj = (ww + tcap * hr + norm * hz) / (1 - universal)
    return high * jj + sqrt_upper(150 * high) + 12 * high


def run_certificate():
    model_extension()
    radius = F(17, 100)
    assert F(1, 4) - radius**2 > F(47, 100)**2
    tail = high_area_tail(radius)
    print('exact high-area tail norm upper', str(tail), 'decimal', float(tail), flush=True)
    assert tail < 1
    rows = [(quadratic_cell(F(index, 160), F(index + 1, 160), radius), index) for index in range(160)]
    upper, index = max(rows)
    print('quadratic completion max', float(upper), 'cell', index, 'target', float(1 / radius**2), flush=True)
    assert upper < 1 / radius**2
    assert 25 / (4 * (F(16, 27) - F(1, 20))) < 12
    print('PASS: tail<1, extended model margin, and 160 whole-q nonlinear completion cells (with the separate four-coefficient envelope certificate).', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', required=True, action='store_true')
    parser.parse_args()
    run_certificate()
