#!/usr/bin/env python3
"""Independent near35deg area comparison: positive recurrences and Cauchy tails.
Version 0.10 — program b, 20261101__22:03 EST. Different96/246 parameter cells, dyadic Newton upper roots, no author code.
"""

import argparse
import json
from fractions import Fraction as Rat
from functools import lru_cache
import sympy as sp
from EUC_B3_check_b import product, geometric_tails
from EUC_B4_check_b import add_polynomials, polynomial_power, rational_coefficients


@lru_cache(maxsize=2048)
def root_upper(value):
    if value == 0:
        return Rat(0)
    scale, upper = 2**30, max(Rat(1), value)
    for _ in range(20):
        newton = (upper+value/upper)/2
        upper = Rat((newton.numerator*scale+newton.denominator-1)//newton.denominator, scale)
    assert upper*upper >= value
    return upper


@lru_cache(maxsize=1024)
def coefficients(kappa, beta, first, second, exponent):
    degree = 48
    aa, bb = [0, Rat(4, 3), -Rat(8, 3)], [0, 0, Rat(16, 15)]
    if exponent == 3:
        budget = add_polynomials([first*value for value in aa], [second*value for value in bb])
        prefactor = 2
    else:
        budget = add_polynomials([first*value for value in product(aa, bb)],
                                 [second*value for value in product(bb, bb)])
        prefactor = 3
    numerator = product(product([0, prefactor], [1, Rat(2, 3)]), budget)
    numerator = product(numerator, [1, -4, 4])
    denominator = polynomial_power([1, -(2+kappa), 2*kappa-beta], exponent)
    return tuple(rational_coefficients(numerator, denominator, degree))


def majorant_value(point, kappa, beta, first, second, exponent):
    aa, bb = Rat(4, 3)*point, Rat(16, 15)*point**2/(1-2*point)
    denominator = 1-kappa*point-beta*point**2/(1-2*point)
    assert denominator > 0
    budget = first*aa+second*bb if exponent == 3 else first*aa*bb+second*bb**2
    return (2 if exponent == 3 else 3)*point*(1+Rat(2, 3)*point)*budget/denominator**exponent


def series_operators(coeffs, circle_bound, radius):
    degree = len(coeffs)-1
    geometric, weighted = geometric_tails(4*radius, degree)  # Larger circle is1/4.
    h_partial = sum(coeffs[index]*radius**(index-1) for index in range(3, degree+1, 2))
    w_tail = sum((index+Rat(7, 3))*coeffs[index]*radius**(index-3) for index in range(5, degree+1, 2))
    w_tail += sum(Rat(index, 2)*coeffs[index]*radius**(index-4) for index in range(6, degree+1, 2))
    h_over_tail = sum(coeffs[index]*radius**(index-3) for index in range(5, degree+1, 2))
    h_upper = h_partial+circle_bound/radius*geometric
    w_upper = w_tail+circle_bound/radius**4*(weighted+3*geometric)
    h_over_upper = h_over_tail+circle_bound/radius**3*geometric
    return h_upper, w_upper, h_over_upper


def parameter_caps(low, high, defect):
    kappa = (min(Rat(2), root_upper(Rat(16, 9)*(Rat(21, 40)**2+(Rat(1, 2)-low)*defect)))
             if low < Rat(1, 2) else Rat(7, 10))
    eta = min(Rat(1), high*defect)
    return kappa, Rat(16, 15)*root_upper(eta), root_upper(eta)


def model_caps(kappa, size):
    cc = 2*kappa**3+Rat(20, 3)*kappa**2+Rat(32, 9)*kappa
    cp = 6*kappa**2+Rat(40, 3)*kappa+Rat(32, 9)
    aa = kappa**4+Rat(4, 3)*kappa**3
    ap = 4*kappa**3+4*kappa**2
    denominator = 1-Rat(4, 3)*kappa*size-aa*size**2
    assert denominator > 0
    numerator = cc+Rat(16, 3)*aa*size
    derivative = (cp+2*aa*size+Rat(16, 3)*ap*size)/denominator
    derivative += numerator*(Rat(4, 3)*size+ap*size**2)/denominator**2
    return numerator/denominator, Rat(2, 3)*derivative


def strengthened_linear():
    midpoint = sp.Symbol('t')
    polynomial = 4864*midpoint**8+2448*midpoint**7-7632*midpoint**6-5422*midpoint**5+3668*midpoint**4
    polynomial += 4358*midpoint**3+22*midpoint**2-1204*midpoint-337
    denominator = 9*(1-midpoint**2)*(8*midpoint+5)**2*(4-7*midpoint**2)**2
    lower, upper = sp.Rational(19, 40), sp.Rational(1, 2)
    for sign in [-1, 1]:
        target = sp.Poly(sp.expand(sp.Rational(19, 2)*denominator+sign*64*polynomial), midpoint)
        assert target.eval(lower) > 0 and target.eval(upper) > 0
        assert target.count_roots(lower, upper) == 0
    radius, size, qmax = Rat(3, 20), Rat(9, 400), Rat(1, 5)
    assert (1-Rat(4, 3)*size)/(1+Rat(40, 59)**2*size)**2 > Rat(19, 20)
    assert 16*size/(9+28*size) < qmax*qmax
    assert 1+Rat(32, 3)*size < Rat(81, 64)
    assert Rat(9, 8)+2*Rat(4, 5)*qmax < Rat(3, 2)
    assert 64*(1-2*Rat(19, 40))*3*12/(9*Rat(3, 4)*(8*Rat(19, 40)+5)**2) < Rat(1, 4)
    # j=n+4: (j+3/2)^2/(2j-1) <= (4/7)n+121/28,
    # since the cleared difference is n^2/7+23n/14 >=0.
    tail = (Rat(64, 27)/Rat(19, 20))**2*Rat(4, 7)*qmax**2
    tail *= qmax**2/(1-qmax**2)**2+Rat(121, 16)/(1-qmax**2)
    assert tail < Rat(6, 5)
    assert Rat(1, 48)+Rat(361, 20)+tail < Rat(81, 4)


def run_tests():
    strengthened_linear()
    radius, size, larger = Rat(3, 20), Rat(9, 400), Rat(1, 4)
    uniform = Rat(16, 3)*size/(1-4*size)**2+4*size/(1-4*size)
    assert uniform < 1
    # Uniform larger-circle Cauchy constants dominate every positive cell series.
    cm = majorant_value(larger, Rat(2), Rat(16, 15), Rat(1), Rat(1), 3)
    cr = majorant_value(larger, Rat(2), Rat(16, 15), Rat(1), Rat(1), 4)
    mb = coefficients(Rat(40, 59), Rat(0), Rat(0), Rat(1), 3)
    hb, _, hb_over_tail = series_operators(mb, cm, radius)
    small = []
    for index in range(96):
        low, high = Rat(index, 96), Rat(index+1, 96)
        peak = Rat(1, 4) if low <= Rat(1, 2) <= high else max(low*(1-low), high*(1-high))
        gamma = min(Rat(1), 2*root_upper(peak))
        defect = min(Rat(1), 4*(1-low))
        kappa, beta, _ = parameter_caps(low, high, defect)
        remainder = coefficients(kappa, beta, gamma, high, 4)
        majorant = coefficients(kappa, beta, root_upper(1-low), root_upper(high), 3)
        hr, wr, _ = series_operators(remainder, cr, radius)
        dh, _, _ = series_operators(majorant, cm, radius)
        tcap, lip = model_caps(kappa, size)
        wtail = wr+Rat(4, 3)*gamma*hb_over_tail
        jj = 6*gamma+(wtail+tcap*hr+Rat(9, 2)*root_upper(high)*dh+gamma*lip*hb+6*gamma*uniform)/(1-uniform)
        score = jj+10*high
        assert score < 41
        small.append((score, index))
    large = []
    for eindex in range(12):
        low_e, high_e = 1+Rat(eindex, 4), 1+Rat(eindex+1, 4)
        for qindex in range(48):
            low, high = Rat(qindex, 48), Rat(qindex+1, 48)
            if low_e > 4*(1-low):
                continue
            kappa, beta, root_eta = parameter_caps(low, high, high_e)
            zz = coefficients(kappa, beta, Rat(0), Rat(1), 3)
            hz, vz, _ = series_operators(zz, cm, radius)
            c2 = Rat(128, 27)*(4*root_upper(high_e*(1-low))+Rat(1, 200))
            c3 = Rat(256, 27)
            leading = root_upper(c2*c2/3+c3*c3/5)
            tcap, _ = model_caps(kappa, size)
            ratio = size*root_eta*(leading+vz+tcap*hz)/((1-uniform)*low_e)
            assert ratio < Rat(5, 6)
            large.append((ratio, eindex, qindex))
    assert len(large) == 246
    assert Rat(81, 4)/(4*(Rat(16, 27)-Rat(1, 20))) < 10
    assert 44*size < 1
    print(json.dumps(dict(status='PASS', method='96/246 new cells; 48-term positive recurrences plus rigorous Cauchy tails; dyadic Newton upper roots',
                          small_cells=len(small), small_max=float(max(small)[0]), small_max_index=max(small)[1],
                          large_cells=len(large), large_max=float(max(large)[0]), large_max_indices=max(large)[1:]), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.parse_args()
    run_tests()


if __name__ == '__main__':
    main()
