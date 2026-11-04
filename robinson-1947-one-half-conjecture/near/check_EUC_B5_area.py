#!/usr/bin/env python3
"""Robinson 1947, program a: exact arithmetic for area comparison at y<=3/20.
Version 0.30. Exact margins below 41 and 5/6.
"""
import argparse
from fractions import Fraction as F
from math import isqrt
import json


def sqrt_upper(value):
    scale = 10**6
    root = isqrt(value.numerator * scale**2 // value.denominator)
    return F(root if F(root, scale)**2 == value else root + 1, scale)


def value_derivative(point, kappa, beta, first, second, exponent):
    aa, aap = F(4, 3) * point, F(4, 3)
    bb = F(16, 15) * point**2 / (1 - 2 * point)
    bbp = F(16, 15) * (2 * point - 2 * point**2) / (1 - 2 * point)**2
    if exponent == 4:
        budget = first * aa * bb + second * bb**2
        budgetp = first * (aap * bb + aa * bbp) + 2 * second * bb * bbp
        factor = 3
    else:
        budget = first * aa + second * bb
        budgetp = first * aap + second * bbp
        factor = 2
    den = 1 - kappa * point - beta * point**2 / (1 - 2 * point)
    assert den > 0
    denp = -kappa - beta * (2 * point - 2 * point**2) / (1 - 2 * point)**2
    numerator = factor * point * (1 + F(2, 3) * point) * budget
    numeratorp = factor * ((1 + F(4, 3) * point) * budget + point * (1 + F(2, 3) * point) * budgetp)
    return numerator / den**exponent, numeratorp / den**exponent - exponent * numerator * denp / den**(exponent + 1)


def parity_values(radius, *parameters):
    plus, plusp = value_derivative(radius, *parameters)
    minus, minusp = value_derivative(-radius, *parameters)
    return (plus - minus) / 2, (plusp + minusp) / 2, (plusp - minusp) / 2


def model_caps(kappa, size):
    zz = kappa
    cc = 2 * zz**3 + F(20, 3) * zz**2 + F(32, 9) * zz
    ccp = 6 * zz**2 + F(40, 3) * zz + F(32, 9)
    aa = zz**4 + F(4, 3) * zz**3
    aap = 4 * zz**3 + 4 * zz**2
    den = 1 - F(4, 3) * zz * size - aa * size**2
    assert den > 0
    numerator = cc + F(16, 3) * aa * size
    tcap = numerator / den
    lip = F(2, 3) * ((ccp + 2 * aa * size + F(16, 3) * aap * size) / den + numerator * (F(4, 3) * size + aap * size**2) / den**2)
    return tcap, lip


def gamma_upper(low, high):
    peak = max(low * (1 - low), high * (1 - high))
    if low <= F(1, 2) <= high:
        peak = F(1, 4)
    return 2 * sqrt_upper(peak)


def parameter_caps(low, high, defect_high):
    kappa = min(F(2), sqrt_upper(F(16, 9) * (F(21, 40)**2 + (F(1, 2) - low) * defect_high))) if low < F(1, 2) else F(7, 10)
    eta = min(F(1), high * defect_high)
    return kappa, F(16, 15) * sqrt_upper(eta), sqrt_upper(eta)


def small_defect_bound(low, high, radius):
    size = radius**2
    gamma = gamma_upper(low, high)
    defect_high = min(F(1), 4 * (1 - low))
    kappa, beta, _ = parameter_caps(low, high, defect_high)
    odd, oddp, evenp = parity_values(radius, kappa, beta, gamma, high, 4)
    hr = odd / radius
    vtail = (radius * oddp + F(7, 3) * odd) / radius**3 + evenp / (2 * radius**3)
    b_odd, _, _ = parity_values(radius, F(40, 59), F(0), F(0), F(1), 3)
    bh = b_odd / radius
    vtail += F(4, 3) * gamma * bh / size - F(512, 45) * gamma
    assert vtail >= 0
    full_odd, _, _ = parity_values(radius, kappa, beta, sqrt_upper(1 - low), sqrt_upper(high), 3)
    dh = full_odd / radius
    universal = F(16, 3) * size / (1 - 4 * size)**2 + 4 * size / (1 - 4 * size)
    tcap, lip = model_caps(kappa, size)
    jj = 6 * gamma + (vtail + tcap * hr + F(9, 2) * sqrt_upper(high) * dh + gamma * lip * bh + 6 * gamma * universal) / (1 - universal)
    return jj + 10 * high


def large_defect_bound(low, high, defect_low, defect_high, radius):
    size = radius**2
    kappa, beta, sqrt_eta = parameter_caps(low, high, defect_high)
    odd, oddp, evenp = parity_values(radius, kappa, beta, F(0), F(1), 3)
    hh = odd / radius
    vtail = (radius * oddp + F(7, 3) * odd) / radius**3 + evenp / (2 * radius**3)
    vtail -= F(1024, 45) + F(64, 5) * kappa
    assert vtail >= 0
    cc2 = F(128, 27) * (4 * sqrt_upper(defect_high * (1 - low)) + F(1, 200))
    cc3 = F(256, 27)
    cleading = sqrt_upper(cc2**2 / 3 + cc3**2 / 5)
    tcap, _ = model_caps(kappa, size)
    universal = F(16, 3) * size / (1 - 4 * size)**2 + 4 * size / (1 - 4 * size)
    return size * sqrt_eta * (cleading + vtail + tcap * hh) / ((1 - universal) * defect_low)


def run_certificate():
    radius = F(3, 20)
    small_rows = [(small_defect_bound(F(index, 80), F(index + 1, 80), radius), index) for index in range(80)]
    small_max, small_index = max(small_rows)
    assert small_max < 41 < 44, (float(small_max), small_index)
    large_rows = []
    for eindex in range(12):
        elo, ehi = 1 + F(eindex, 4), 1 + F(eindex + 1, 4)
        for qindex in range(40):
            qlo, qhi = F(qindex, 40), F(qindex + 1, 40)
            if elo > 4 * (1 - qlo):
                continue
            ratio = large_defect_bound(qlo, qhi, elo, ehi, radius)
            large_rows.append((ratio, eindex, qindex))
    large_max, eindex, qindex = max(large_rows)
    assert large_max < F(5, 6) < 1, (float(large_max), eindex, qindex)
    assert F(81, 4) / (4 * (F(16, 27) - F(1, 20))) < 10
    assert 44 < 1 / radius**2
    print(json.dumps({'status': 'PASS', 'small_cells': len(small_rows), 'small_max': str(small_max), 'small_max_decimal': float(small_max), 'small_max_index': small_index, 'large_cells': len(large_rows), 'large_max_ratio': str(large_max), 'large_max_decimal': float(large_max), 'large_max_indices': [eindex, qindex]}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', required=True, action='store_true')
    parser.parse_args()
    run_certificate()
