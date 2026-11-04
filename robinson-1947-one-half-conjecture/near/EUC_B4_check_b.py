#!/usr/bin/env python3
"""Independent B4 audit: direct linear area variations and rigorous all-order tails.
Version 0.20 — program b, 20261101__21:24 ET. Exact quadratic-field area variations avoid multivariate expression expansion; no author code.
"""

import argparse
import json
from fractions import Fraction as Rat
import sympy as sp
from sympy.polys.fields import field
from EUC_B3_check_b import product, geometric_tails


def add_polynomials(left, right):
    return [(left[index] if index < len(left) else 0)+(right[index] if index < len(right) else 0)
            for index in range(max(len(left), len(right)))]


def polynomial_power(coefficients, exponent):
    result = [Rat(1)]
    for _ in range(exponent):
        result = product(result, coefficients)
    return result


def rational_coefficients(numerator, denominator, degree):
    result = []
    for index in range(degree+1):
        current = numerator[index] if index < len(numerator) else 0
        current -= sum(denominator[offset]*result[index-offset]
                       for offset in range(1, min(index, len(denominator)-1)+1))
        result.append(current/denominator[0])
    assert all(value >= 0 for value in result)
    return result


def rational_majorants(degree):
    linear, tail = Rat(91, 100), Rat(32, 45)
    denominator = [Rat(1), -(2+linear), 2*linear-tail]
    aa, bb = [0, Rat(4, 3), -Rat(8, 3)], [0, 0, Rat(16, 15)]
    budget = add_polynomials(add_polynomials(product(aa, aa), product(aa, bb)), product(bb, bb))
    remainder_numerator = product(product([0, 3], [1, Rat(2, 3)]), budget)
    remainder_numerator = product(remainder_numerator, [1, -4, 4])
    majorant_numerator = product(product([0, 2], [1, Rat(2, 3)]), add_polynomials(aa, bb))
    majorant_numerator = product(majorant_numerator, [1, -4, 4])
    remainder = rational_coefficients(remainder_numerator, polynomial_power(denominator, 4), degree)
    majorant = rational_coefficients(majorant_numerator, polynomial_power(denominator, 3), degree)
    return remainder, majorant


def all_order_upper_bound():
    degree, endpoint, larger = 60, Rat(13, 100), Rat(1, 4)
    remainder, majorant = rational_majorants(degree)
    linear, tail = Rat(91, 100), Rat(32, 45)
    aa, bb = Rat(4, 3)*larger, Rat(16, 15)*larger**2/(1-2*larger)
    denominator = 1-linear*larger-tail*larger**2/(1-2*larger)
    assert denominator > 0
    rlarge = 3*larger*(1+Rat(2, 3)*larger)*(aa*aa+aa*bb+bb*bb)/denominator**4
    mlarge = 2*larger*(1+Rat(2, 3)*larger)*(aa+bb)/denominator**3
    dh = sum(majorant[index]*endpoint**(index-1) for index in range(3, degree+1, 2))
    hr = sum(remainder[index]*endpoint**(index-1) for index in range(3, degree+1, 2))
    wt = sum(((index+1)*remainder[index]+Rat(8, 3)*majorant[index])*endpoint**(index-3)
             for index in range(5, degree+1, 2))
    wt += sum(Rat(index, 2)*remainder[index]*endpoint**(index-4)
              for index in range(6, degree+1, 2))
    geometric, weighted = geometric_tails(endpoint/larger, degree)
    dh_error, hr_error = mlarge/endpoint*geometric, rlarge/endpoint*geometric
    wt_error = rlarge/endpoint**4*(weighted+geometric)+Rat(8, 3)*mlarge/endpoint**3*geometric
    qvalue = 4*endpoint**2
    uniform = Rat(4, 3)*qvalue/(1-qvalue)**2+qvalue/(1-qvalue)
    lower = (wt+7*hr+15*dh+14*uniform)/(1-uniform)
    error = (wt_error+7*hr_error+15*dh_error)/(1-uniform)
    assert lower+error < 61
    assert remainder[3] == Rat(16, 3)
    assert remainder[4] == Rat(64, 15)+Rat(32, 9)+Rat(64, 3)*linear
    assert majorant[3] == Rat(176, 45)+8*linear
    return lower, lower+error, uniform


def certify_positive(polynomial, variable):
    polynomial = sp.Poly(sp.expand(polynomial), variable, domain=sp.QQ)
    lower, upper = sp.Rational(12, 25), sp.Rational(1, 2)
    assert polynomial.eval(lower) > 0 and polynomial.eval(upper) > 0
    assert polynomial.count_roots(lower, upper) == 0


class OuterPair:
    """Exact field Q(t)[h]/(h^2-t^2+1/4); two coefficients, no expression swell."""

    def __init__(self, first, second, relation):
        self.first, self.second, self.relation = first, second, relation

    def convert(self, other):
        return other if isinstance(other, OuterPair) else OuterPair(other, 0, self.relation)

    def __add__(self, other):
        other = self.convert(other)
        return OuterPair(self.first+other.first, self.second+other.second, self.relation)

    __radd__ = __add__

    def __neg__(self):
        return OuterPair(-self.first, -self.second, self.relation)

    def __sub__(self, other):
        return self+-self.convert(other)

    def __rsub__(self, other):
        return -self+self.convert(other)

    def __mul__(self, other):
        other = self.convert(other)
        return OuterPair(self.first*other.first+self.relation*self.second*other.second,
                         self.first*other.second+self.second*other.first, self.relation)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.convert(other)
        denominator = other.first**2-self.relation*other.second**2
        return self*OuterPair(other.first/denominator, -other.second/denominator, self.relation)

    def __rtruediv__(self, other):
        return self.convert(other)/self

    def __pow__(self, exponent):
        result = self.convert(1)
        for _ in range(exponent):
            result = result*self
        return result

    def opposite(self):
        return OuterPair(self.first, -self.second, self.relation)


def direct_area_variations():
    rational_field, parameter = field('t', sp.QQ)
    relation = parameter**2-rational_field(1)/4
    increment = OuterPair(rational_field.zero, rational_field.one, relation)
    constant = lambda value: OuterPair(value, rational_field.zero, relation)
    midpoint_pair = constant(parameter)
    variance = constant(1-parameter**2)
    linear, other = constant(1/(1+parameter)), midpoint_pair/variance
    base = increment*(1+other*increment)/(1-linear*increment)**2
    prime = (1+(2*other+linear)*increment)/(1-linear*increment)**3
    span = base-base.opposite()
    quotient = 1+((-midpoint_pair+increment)*prime-(-midpoint_pair-increment)*prime.opposite())/span
    midpoint = sp.Symbol('t')
    variance_expr = 1-midpoint**2
    u2 = 64*(1-2*midpoint)*(4*midpoint+1)*(10*midpoint+7)/(9*variance_expr*(8*midpoint+5)**2)
    p8 = 4864*midpoint**8+2448*midpoint**7-7632*midpoint**6-5422*midpoint**5+3668*midpoint**4
    p8 += 4358*midpoint**3+22*midpoint**2-1204*midpoint-337
    den = 9*variance_expr*(8*midpoint+5)**2*(4-7*midpoint**2)**2
    u3 = -64*p8/den
    for index, target in [(2, u2), (3, u3)]:
        tail_increment = increment**index/(variance*(variance+midpoint_pair*increment)**(index-1))
        first_variation = -2*increment*(1+other*increment)*tail_increment/(1-linear*increment)**3
        logarithmic_derivative = (index+1)/increment+other/(1+other*increment)
        logarithmic_derivative -= (index-1)*midpoint_pair/(variance+midpoint_pair*increment)
        logarithmic_derivative += 3*linear/(1-linear*increment)
        variation_prime = first_variation*logarithmic_derivative
        change = (-midpoint_pair+increment)*variation_prime-(-midpoint_pair-increment)*variation_prime.opposite()
        change -= (quotient-1)*(first_variation-first_variation.opposite())
        derivative = change/span/constant(relation)
        assert derivative.second == 0
        assert sp.factor(derivative.first.as_expr()-target) == 0
    certify_positive(10*den+64*p8, midpoint)
    certify_positive(10*den-64*p8, midpoint)


def run_tests():
    direct_area_variations()
    low, high, uniform = all_order_upper_bound()
    size, diagonal = Rat(169, 10000), Rat(600, 481)
    assert Rat(1, 4)-size > Rat(12, 25)**2
    assert Rat(625, 1369)+Rat(8, 9)*Rat(2, 5) < Rat(91, 100)**2
    assert (1-Rat(4, 3)*size)/(1+Rat(625, 1369)*size)**2 > Rat(19, 20)
    qvalue = Rat(17, 100)
    tail = (Rat(64, 27)/Rat(19, 20))**2*2*qvalue**2*(4-3*qvalue**2)/(1-qvalue**2)**2
    assert tail < 2 and Rat(1, 3)+20+tail < 25
    assert Rat(128, 27)*(Rat(27, 25)+Rat(2, 3)+Rat(7, 6)) < 14
    small = Rat(16, 27)-25*size/(4*(diagonal-61*size))
    assert small == Rat(11777669, 112468068) > Rat(1, 20)
    for defect, cap in [(Rat(1, 2), 0), (Rat(1), 1), (Rat(4), 14)]:
        bracket = -Rat(11, 8)+Rat(27, 100)*defect+defect**2/8+Rat(7, 6)
        assert bracket < 0 if cap == 0 else Rat(128, 27)*bracket < cap
    qphysical = 4*size
    vtail = Rat(16, 9)*(12*(1+qphysical)/(1-qphysical)**3+28/(1-qphysical)**2+15/(1-qphysical))-Rat(880, 9)
    lower_h = 1-uniform
    assert lower_h > Rat(4, 5)
    finishes = []
    for cost, absolute, defect_root in [(0, 30, Rat(63, 100)), (1, 35, Rat(7, 10)), (14, None, Rat(1))]:
        quadratic = diagonal-cost*size
        linear = Rat(9, 2)+(absolute*uniform/lower_h if absolute is not None else 0)
        constant = ((5 if absolute is not None else 63)*uniform+vtail)/lower_h
        assert 2*quadratic*defect_root-size*linear > 0
        value = quadratic*defect_root**2-size*linear*defect_root-size*constant
        assert value > size/20
        finishes.append(float(value))
    print(json.dumps(dict(status='PASS', method='direct symbolic variations, exact Sturm positivity, 60-term recurrence plus Cauchy tails',
                          J_lower=float(low), J_upper=float(high), J_tail_error=float(high-low),
                          small_coefficient=str(small), coarse_endpoints=finishes), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.parse_args()
    run_tests()


if __name__ == '__main__':
    main()
