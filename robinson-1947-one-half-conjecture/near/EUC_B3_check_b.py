#!/usr/bin/env python3
"""Independent Euclidean B3 audit: rational recurrence + geometric Cauchy tails.
Version 0.10 — program b, 20261101__20:46 ET. Imports no author code.
Unlike the author's odd/even rational-function endpoint formulas, this computes
40 coefficients of a degree6 rational recurrence, then bounds the INFINITE
remainder on a larger circle of radius1/4 by positivity and geometric sums.
"""

import argparse
import json
from fractions import Fraction as Rat
import sympy as sp


def product(left, right):
    coefficients = [Rat(0)]*(len(left)+len(right)-1)
    for first, value in enumerate(left):
        for second, other in enumerate(right):
            coefficients[first+second] += value*other
    return coefficients


def majorant_coefficients(linear, tail, degree):
    quadratic = [Rat(1), -(2+linear), 2*linear-tail]
    denominator = product(product(quadratic, quadratic), quadratic)
    numerator = product(product([0, 2], [1, Rat(2, 3)]), [0, Rat(4, 3), -Rat(8, 5)])
    numerator = product(numerator, [1, -4, 4])
    coefficients = []
    for index in range(degree+1):
        current = numerator[index] if index < len(numerator) else 0
        current -= sum(denominator[offset]*coefficients[index-offset]
                       for offset in range(1, min(index, len(denominator)-1)+1))
        coefficients.append(current)
    assert all(value >= 0 for value in coefficients)
    return coefficients


def geometric_tails(ratio, degree):
    """Sum of ratio**n, and n*ratio**n, for n strictly greater than degree."""
    geometric = ratio**(degree+1)/(1-ratio)
    weighted = geometric*(degree+1+ratio/(1-ratio))
    return geometric, weighted


def independent_tails(linear, tail):
    degree, point, larger = 40, Rat(1, 10), Rat(1, 4)
    coefficients = majorant_coefficients(linear, tail, degree)
    increment = Rat(4, 3)*larger+Rat(16, 15)*larger**2/(1-2*larger)
    denominator = 1-linear*larger-tail*larger**2/(1-2*larger)
    assert denominator > 0
    larger_bound = 2*larger*(1+Rat(2, 3)*larger)*increment/denominator**3
    dh_partial = sum(coefficients[index]*point**(index-1) for index in range(3, degree+1, 2))
    b_partial = sum((index+Rat(7, 3))*coefficients[index]*point**(index-3)
                    for index in range(5, degree+1, 2))
    b_partial += sum(Rat(index, 2)*coefficients[index]*point**(index-4)
                     for index in range(6, degree+1, 2))
    koebe_ratio = Rat(25, 37)
    b_partial += Rat(8, 3)*sum(2*index*koebe_ratio**(index-1)*point**(index-3)
                              for index in range(5, degree+1, 2))
    geometric, weighted = geometric_tails(point/larger, degree)
    dh_error = larger_bound/point*geometric
    # Combine both parities into a single deliberately larger Cauchy tail.
    b_error = larger_bound/point**4*(weighted+4*geometric)
    _, koebe_weighted = geometric_tails(koebe_ratio*point, degree)
    b_error += Rat(16, 3)/(koebe_ratio*point**3)*koebe_weighted
    return dh_partial, dh_partial+dh_error, b_partial, b_partial+b_error


def symbolic_identities():
    midpoint, defect, imag, coefficient, area3, area5 = sp.symbols('t e a A b3 b5', real=True)
    variance = 1-midpoint**2
    third = 3*coefficient**2/4-2*area3
    fourth = coefficient**3/2-3*coefficient*area3-2*area5
    physical2 = (coefficient-midpoint)/variance
    physical3 = (midpoint**2-2*coefficient*midpoint+third)/variance**2
    physical4 = (-midpoint**3+3*coefficient*midpoint**2-3*third*midpoint+fourth)/variance**3
    leading = (2+2*midpoint*physical2)*physical3-4*midpoint*physical4
    polynomial = -midpoint*coefficient**3/4+(sp.Rational(3, 4)+midpoint**2)*coefficient**2
    polynomial -= midpoint*(2+midpoint**2)*coefficient
    polynomial += midpoint**2
    claimed = 2/variance**3*(polynomial+(4*midpoint*(coefficient-2)-2*(1-2*midpoint)**2)*area3+4*midpoint*area5)
    assert sp.expand(sp.together(leading-claimed)) == 0
    variation = sp.expand(sp.re(polynomial.subs(coefficient, 2-defect+sp.I*imag)-polynomial.subs(coefficient, 2)))
    linear = 3-5*midpoint+4*midpoint**2-midpoint**3
    quadratic = sp.Rational(3, 4)-3*midpoint/2+midpoint**2
    target = -linear*defect+quadratic*(defect**2-imag**2)+midpoint*defect**3/4-3*midpoint*defect*imag**2/4
    assert sp.expand(variation-target) == 0
    # Derive the baseline quotient directly from k(z), without the author's formula.
    half_difference = sp.symbols('h')
    first, second = -midpoint+half_difference, -midpoint-half_difference
    koebe = lambda value: value/(1-value)**2
    derivative = lambda value: (1+value)/(1-value)**3
    quotient = sp.factor(1+(first*derivative(first)-second*derivative(second))/(koebe(first)-koebe(second)))
    numerator, denominator = sp.fraction(quotient)
    numerator = sp.rem(numerator, half_difference**2-(midpoint**2-sp.Rational(1, 4)), half_difference)
    denominator = sp.rem(denominator, half_difference**2-(midpoint**2-sp.Rational(1, 4)), half_difference)
    baseline = (sp.Rational(1, 2)-midpoint)/(sp.Rational(3, 4)*(sp.Rational(5, 4)+2*midpoint))
    assert sp.factor(numerator/denominator-baseline) == 0


def run_tests():
    symbolic_identities()
    size, diagonal, baseline = Rat(1, 100), Rat(600, 481), Rat(16, 27)
    hkoebe, hgeneral = Rat(39, 40), Rat(9, 10)
    regimes = [(Rat(1, 16), Rat(1, 4), Rat(3, 4), Rat(4, 15), 24, Rat(3, 25), 10, 16, 12),
               (Rat(1, 4), Rat(1, 2), Rat(5, 6), Rat(8, 15), 29, Rat(3, 25), 16, 22, 14),
               (Rat(1), Rat(1), Rat(7, 6), Rat(16, 15), 40, Rat(4, 25), 36, 43, 22)]
    records = []
    for emax, sqrt_emax, linear, tail, absolute_c, dh_cap, b_cap, kcap, jcap in regimes:
        low_dh, upper_dh, low_b, upper_b = independent_tails(linear, tail)
        assert 0 < low_dh <= upper_dh < dh_cap
        assert 0 < low_b <= upper_b < b_cap
        assert Rat(625, 1369)+Rat(8, 9)*emax < linear**2
        absolute_bound = Rat(256, 27)*(Rat(3, 2)+Rat(27, 50)*sqrt_emax+emax/2)
        absolute_bound += Rat(896, 81)*sqrt_emax+Rat(9, 2)
        assert absolute_bound < absolute_c
        kbound = (Rat(9, 2)+b_cap)/hkoebe+6*dh_cap/(hkoebe*hgeneral)
        jbound = 7/hkoebe+(absolute_c+b_cap)*dh_cap/(hkoebe*hgeneral)
        assert kbound < kcap and jbound < jcap
        records.append(dict(e_max=str(emax), dh_upper=float(upper_dh), b_upper=float(upper_b),
                            dh_tail=float(upper_dh-low_dh), b_tail=float(upper_b-low_b)))
    assert Rat(128, 27)*(Rat(7, 3)-Rat(49, 50)) < 7
    assert Rat(128, 27)*(Rat(6, 125)+Rat(9, 10)) < Rat(9, 2)
    assert (1-Rat(4, 3)*size)/(1+Rat(625, 1369)*size)**2 > hkoebe
    qvalue = 4*size
    assert Rat(4, 3)*qvalue/(1-qvalue)**2+qvalue/(1-qvalue) == Rat(43, 432)
    assert Rat(43, 432) < Rat(1, 10)
    small = baseline-Rat(16**2)*size/(4*(diagonal-12*size))
    assert small == Rat(3040, 122013) and small > Rat(1, 50)
    for kcap, jcap, defect_lower in [(22, 14, Rat(1, 4)), (43, 22, Rat(1, 2))]:
        assert 2*(diagonal-jcap*size)*defect_lower-kcap*size > 0
        endpoint = baseline*size+(diagonal-jcap*size)*defect_lower**2-kcap*size*defect_lower
        assert endpoint > size/50
    coarse = Rat(16, 9)*(12*(1+qvalue)/(1-qvalue)**3+28/(1-qvalue)**2+15/(1-qvalue))
    assert coarse/hgeneral < 120
    assert diagonal-120*size == Rat(114, 2405) > size/50
    print(json.dumps(dict(status='PASS', method='40-term rational recurrence plus rigorous larger-circle tail',
                          regimes=records, small_case_coefficient=str(small)), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.parse_args()
    run_tests()


if __name__ == '__main__':
    main()
