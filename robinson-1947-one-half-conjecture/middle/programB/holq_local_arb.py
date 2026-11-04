#!/usr/bin/env python3
"""Independent Arb/Hessian check of Program A's exact HOLQ local boxes.
Version 0.20 — Program B, 20261101__22:52 ET. Expose exact rectangular-box
enclosures for independent tree replay; unchanged dual-form AD2 arithmetic.
No C++ code imported; no global sector or new compute ticket.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import time
from flint import arb, acb, ctx
from arb_differential import SecondDifferential
from fourlog_arb_box import closed_ball, norm_square, real_square, require_positive


def cosine(value):
    positive, negative = (acb(0, 1)*value).exp(), (-acb(0, 1)*value).exp()
    return (positive+negative)/2


def sine(value):
    return ((acb(0, 1)*value).exp()-(-acb(0, 1)*value).exp())/acb(0, 2)


def exact_intersection(first, second):
    if not first.is_finite() or not second.is_finite():
        raise ArithmeticError('nonfinite independent entire formula')
    return SecondDifferential(SecondDifferential.intersect(first.value, second.value),
        [SecondDifferential.intersect(left, right) for left, right in zip(first.gradient, second.gradient)],
        [[SecondDifferential.intersect(first.hessian[row][column], second.hessian[row][column])
          for column in range(5)] for row in range(5)],
        SecondDifferential.intersect(first.center_value, second.center_value),
        [SecondDifferential.intersect(left, right) for left, right in zip(first.center_gradient, second.center_gradient)])


def quotient(balls):
    SecondDifferential.set_box([arb(0, value.rad()) for value in balls]+[arb(0)])
    alpha, psi, omega, theta = [SecondDifferential.variable(value, index) for index, value in enumerate(balls)]
    norm = (arb(1)/2).atanh()
    kernel = ((acb(0, 1)*theta/2).exp()/2).atanh()
    first_square = (norm+kernel.real)/2
    require_positive(first_square, 'first real Gram length not positive')
    first = first_square.sqrt()
    cross = kernel.imag/(2*first)
    determinant = norm*norm-norm_square(kernel)
    require_positive(determinant, 'real Gram determinant not positive')
    last_square = determinant/(2*(norm+kernel.real))
    require_positive(last_square, 'second real Gram length not positive')
    last = last_square.sqrt()
    cos_alpha, sin_alpha = cosine(alpha).real, sine(alpha).real
    diagonal_one = cos_alpha*(acb(0, 1)*(psi+omega)).exp()
    off_diagonal = acb(0, 1)*sin_alpha*(acb(0, 1)*psi).exp()
    diagonal_two = cos_alpha*(acb(0, 1)*(psi-omega)).exp()
    uu = first_square*diagonal_one
    vv = real_square(cross)*diagonal_one+2*cross*last*off_diagonal+last_square*diagonal_two
    ww = first*cross*diagonal_one+first*last*off_diagonal
    denominator = cosine(theta/4).real
    require_positive(denominator, 'tan denominator not positive')
    tau = sine(theta/4).real/denominator
    require_positive(tau, 'positive pair angle required')
    ell_one, ell_two, cross_kernel = 2*(uu-vv)+acb(0, 4)*ww, 2*(uu-vv)-acb(0, 4)*ww, 2*(uu+vv)
    endpoint_one, endpoint_two = ell_one.exp(), ell_two.exp()
    ratio_plus = acb(0, 1)*tau*cross_kernel.exp()
    ratio_inverse = -acb(0, 1)*(-cross_kernel).exp()/tau
    original = 1+(endpoint_one+endpoint_two)/2+(endpoint_one-endpoint_two)*(ratio_plus+ratio_inverse)/4
    normal = 1+(2*(uu-vv)).exp()*cosine(4*ww)
    normal += ((-4*vv).exp()/tau-tau*(4*uu).exp())*sine(4*ww)/2
    return exact_intersection(original, normal).real


def input_bounds(center_strings, radius_string):
    radius = float(radius_string)
    bounds = []
    for entry in center_strings:
        center = float(entry)
        lower = math.nextafter(center-radius, -math.inf)
        upper = math.nextafter(center+radius, math.inf)
        bounds.append([Fraction.from_float(lower), Fraction.from_float(upper)])
    return bounds


def check_endpoints(endpoints):
    balls = [closed_ball(*interval) for interval in endpoints]
    ranges = quotient(balls)
    center = quotient([value.mid() for value in balls])
    radii = [value.rad() for value in balls]
    linear = sum((center.gradient[index].real.abs_upper()*radii[index] for index in range(4)), arb(0))
    absolute, signed = arb(0), arb(0)
    for row in range(4):
        for column in range(4):
            absolute += ranges.hessian[row][column].real.abs_upper()*radii[row]*radii[column]/2
        diagonal = ranges.hessian[row][row].real.lower()
        if diagonal < 0:
            signed += (-diagonal)*radii[row]*radii[row]/2
        for column in range(row):
            signed += ranges.hessian[row][column].real.abs_upper()*radii[row]*radii[column]
    standard_lower = (center.value.real-linear-absolute).lower()
    signed_lower = (center.value.real-linear-signed).lower()
    lower = max(ranges.value.real.lower(), standard_lower, signed_lower)
    return {'status': 'INDEPENDENT_LOCAL_BOX_CONFIRMED' if lower > 0 else 'INCOMPLETE',
            'binary64_outward_endpoints_exact': [[str(lower), str(upper)] for lower, upper in endpoints],
            'center_value': center.value.real.str(40, more=True),
            'natural_lower': ranges.value.real.lower().str(40, more=True),
            'absolute_Taylor_lower': standard_lower.str(40, more=True),
            'signed_Taylor_lower': signed_lower.str(40, more=True),
            'lower': lower.str(40, more=True)}


def check_box(center_strings, radius_string):
    result = check_endpoints(input_bounds(center_strings, radius_string))
    result.update(center_strings=center_strings, radius_string=radius_string)
    return result


def tests():
    for degree in [90, 120]:
        theta = arb(degree)*arb.pi()/180
        left = (acb(0, theta/2)).exp()/2
        right = left.conjugate()
        for sign in [1, -1]:
            actual = quotient([arb(0), arb(0) if sign == 1 else arb.pi(), arb(0), theta])
            value = lambda point: point/(1-sign*point)**2
            derivative = lambda point: (1+sign*point)/(1-sign*point)**3
            expected = 1+(left*derivative(left)-right*derivative(right))/(value(left)-value(right))
            assert (actual.value.real-expected.real).contains(0)
    # Each call separately intersects all values, five first partials and25 second
    # partials of two independently evaluated exact identities, at a complex O.
    quotient([arb('.4'), arb('.7'), arb('-.3'), arb('1.9')])
    print('PASS: Koebe signs and two-form value/gradient/Hessian consistency at complex matrix')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, required=True)
    parser.add_argument('--test', action='store_true')
    parser.add_argument('--output', type=Path)
    arguments = parser.parse_args()
    ctx.prec, ctx.threads = arguments.precision, 1
    if arguments.test:
        tests()
        return
    if arguments.output is None:
        parser.error('--output required outside --test')
    started = time.process_time()
    records = [check_box(['.6160173737963576','1.5707963267948966','1.5707963267948966','1.7453292519943295'],'.03'),
               check_box(['.6427291128458626','1.5707963267948966','1.5707963267948966','2.0943951023931953'],'.05')]
    directory = Path(__file__).resolve().parent
    hashes = {name: hashlib.sha256((directory/name).read_bytes()).hexdigest()
              for name in [Path(__file__).name,'arb_differential.py','fourlog_arb_box.py']}
    result = {'status': 'TWO_LOCAL_BOXES_NOT_A_GLOBAL_SECTOR','records':records,
              'source_hashes':hashes,'cpu_seconds':time.process_time()-started}
    arguments.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
