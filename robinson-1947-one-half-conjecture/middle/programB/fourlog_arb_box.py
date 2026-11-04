#!/usr/bin/env python3
"""Independent validated one-box exclusions for the four-log screen.
Version 1.10 — Program B, 20261101__21:36 ET. Geometry-only mean-value range
for epsilon on the WHOLE angle interval, keeping its raw derivatives unchanged.
One excluded box is not a global certificate. No sustained cover is launched here.
"""
import argparse
import json
from fractions import Fraction
from flint import arb, acb, fmpq, ctx
from arb_differential import Differential, complex_ball, real_square_ball


class UnresolvedEnclosure(ArithmeticError):
    pass


def real_square(value):
    # Generic **2 can return nan on a zero-centered ball in this installation.
    # Absolute endpoint bounds enclose the polynomial tightly, including zero.
    return value.square_real() if isinstance(value, Differential) else real_square_ball(value)


def norm_square(value):
    return real_square(value.real)+real_square(value.imag)


def transpose(matrix):
    return [[matrix[column][row] for column in range(2)] for row in range(2)]


def conjugate(matrix):
    return [[item.conjugate() for item in row] for row in matrix]


def multiply(first, second):
    return [[sum(first[row][index] * second[index][column] for index in range(2))
             for column in range(2)] for row in range(2)]


def quadratic(vector, matrix):
    return sum(vector[row].conjugate()*matrix[row][column]*vector[column]
               for row in range(2) for column in range(2)).real


def dot(first, second):
    return sum(left*right for left, right in zip(first, second))


def require_positive(value, message):
    if not value.is_finite() or not value > 0:
        raise UnresolvedEnclosure(message)


def inverse_metric(first, second, data):
    phase = data['phase']
    first_plus, first_minus = first[0]+phase*first[1], first[0]-phase*first[1]
    second_plus, second_minus = second[0]+phase*second[1], second[0]-phase*second[1]
    return (first_plus.conjugate()*second_plus/(2*data['sum'])
            +first_minus.conjugate()*second_minus/(2*data['gap']))


def inverse_norm(vector, data):
    phase = data['phase']
    return (norm_square(vector[0]+phase*vector[1])/(2*data['sum'])
            +norm_square(vector[0]-phase*vector[1])/(2*data['gap']))


def direct_norm(vector, data):
    phase = data['phase'].conjugate()
    return (data['sum']*norm_square(vector[0]+phase*vector[1])/2
            +data['gap']*norm_square(vector[0]-phase*vector[1])/2)


def geometry(theta, parity):
    endpoint = complex_ball(0, theta/2).exp()/2
    if parity == 'odd':
        norm, kernel = (arb(1)/2).atanh(), endpoint.atanh()
        jet, jet_kernel, derivative_norm = arb(2)/3, endpoint/(1-endpoint**2), arb(10)/9
    else:
        norm, kernel = -(arb(3)/4).log()/2, -(1-endpoint**2).log()/2
        jet, jet_kernel, derivative_norm = arb(1)/3, endpoint**2/(1-endpoint**2), arb(8)/9
    gram = [[acb(norm), kernel.conjugate()], [kernel, acb(norm)]]
    determinant = norm**2 - norm_square(kernel)
    require_positive(determinant, f'{parity} Gram determinant not positive on box')
    inverse = [[acb(norm)/determinant, -kernel.conjugate()/determinant],
               [-kernel/determinant, acb(norm)/determinant]]
    mixed = [[acb(jet), jet_kernel.conjugate()], [jet_kernel, acb(jet)]]
    projection = multiply(inverse, mixed)
    modulus = norm_square(kernel).sqrt()
    require_positive(modulus, f'{parity} kernel modulus not positive')
    data = {'norm': norm, 'kernel': kernel, 'gram': gram, 'inverse_bar': conjugate(inverse),
            'projection': projection, 'mixed': mixed, 'phase': kernel/modulus,
            'sum': norm+modulus, 'gap': determinant/(norm+modulus)}
    residual = derivative_norm-inverse_norm([mixed[0][0].conjugate(), mixed[1][0].conjugate()], data)
    if (isinstance(theta, Differential) and theta.gradient[0] == acb(1)
            and all(item.is_zero() for item in theta.gradient[1:])):
        # epsilon depends ONLY on theta. Its raw derivative encloses d epsilon/d theta
        # everywhere on this interval, regardless of log admissibility. The following
        # range is the ordinary one-dimensional mean-value theorem, not a domain cut.
        angle_ball = theta.value.real
        center_value = geometry(angle_ball.mid(), parity)['residual']
        centered_range = center_value+arb(0, angle_ball.rad())*residual.gradient[0].real
        residual = residual.with_value(centered_range)
    data['residual'] = residual
    return data


def right_log(value, label):
    require_positive(value.real, f'{label} range crosses right-half-plane boundary')
    answer = value.log()
    if not answer.is_finite():
        raise UnresolvedEnclosure(f'{label} logarithm enclosure nonfinite')
    return answer


def logarithm_domain_cuts(value, label):
    # If |Log(value)|<=2log2, then |value|>=1/4 and cos(arg value)>1/8.
    # Hence Re(value)>1/32 and |value|^2<=64 Re(value)^2.
    return {label+'_real_floor': arb(1)/32-value.real,
            label+'_sector': norm_square(value)-64*real_square(value.real)}


def collision_data(theta, logs, branch):
    endpoint = complex_ball(0, theta/2).exp()/2
    exponential = [value.exp() for value in logs]
    for value in exponential:
        require_positive((1+value).real, 'endpoint square-root argument crosses imaginary axis')
    ratio = branch*(1+exponential[1]).sqrt()/(1+exponential[0]).sqrt()
    if not ratio.is_finite():
        raise UnresolvedEnclosure('nonfinite H-ratio enclosure')
    return endpoint, exponential, ratio


def necessary_cuts(theta, logs, branch=1, ratio_override=None, rayleigh=None, even_shift=None):
    """Return rigorous exclusion functions, each of which must be <=0 at a collision.

    If the arithmetic cannot finish, retain ONLY earlier valid cuts and mark the
    remainder unresolved. No interval is narrowed by assuming a desired answer.
    """
    log_three, log_limit = arb(3).log(), 2*arb(2).log()
    cuts = {f'Jenkins_{index+1}': norm_square(value)-log_three**2
            for index, value in enumerate(logs)}
    reason = None
    try:
        endpoint, exponentials, ratio = collision_data(theta, logs, branch)
        if ratio_override is not None:
            ratio = ratio_override
        first, second = exponentials
        opposite = endpoint.conjugate()
        span = endpoint-opposite
        cuts.update({'h_minus_distance': (arb(5)/143)**2-norm_square(ratio-1),
                     'h_plus_distance': (arb(20)/117)**2-norm_square(ratio+1)})
        delta_argument = 2*endpoint/ratio
        cuts.update(logarithm_domain_cuts(delta_argument, 'Delta_argument'))
        difference = right_log(delta_argument, 'Delta_argument')
        cuts['Delta_norm'] = norm_square(difference)-log_limit**2
        root = complex_ball(0, theta/4).exp()*(arb(1)/2).sqrt()
        conjugate_root = root.conjugate()
        positive, negative = (difference/2).exp(), (-difference/2).exp()
        minus_argument = (root*negative-conjugate_root*positive)/(root-conjugate_root)
        plus_argument = (root*negative+conjugate_root*positive)/(root+conjugate_root)
        cuts.update(logarithm_domain_cuts(minus_argument, 'Rminus'))
        cuts.update(logarithm_domain_cuts(plus_argument, 'Rplus'))
        minus_log, plus_log = right_log(minus_argument, 'Rminus'), right_log(plus_argument, 'Rplus')
        cuts.update({'Rminus_log_norm': norm_square(minus_log)-log_limit**2,
                     'Rplus_log_norm': norm_square(plus_log)-log_limit**2})
        cross_odd, cross_even = (minus_log-plus_log)/2, (minus_log+plus_log)/2
        cuts['odd_cross_log_disk'] = 4*norm_square(cross_odd)-log_three**2
        odd_form = [[logs[0]/2, cross_odd], [cross_odd, logs[1]/2]]
        even_form = [[(difference+logs[0])/2, cross_even], [cross_even, (-difference+logs[1])/2]]
        odd = geometry(theta, 'odd')
        columns = [[odd_form[row][column] for row in range(2)] for column in range(2)]
        projected_gram = [[inverse_metric(columns[row], columns[column], odd)
                           for column in range(2)] for row in range(2)]
        if rayleigh is not None:
            denominator_rayleigh = direct_norm(rayleigh, odd)
            if denominator_rayleigh > 0:
                fixed_column = [dot(row, rayleigh) for row in odd_form]
                cuts['odd_fixed_Rayleigh'] = inverse_norm(fixed_column, odd)/denominator_rayleigh-1
        remainder = [[odd['gram'][row][column]-projected_gram[row][column]
                      for column in range(2)] for row in range(2)]
        cuts.update({'odd_PSD_diagonal_1': -remainder[0][0].real,
                     'odd_PSD_diagonal_2': -remainder[1][1].real,
                     'odd_PSD_determinant': norm_square(remainder[0][1])-remainder[0][0].real*remainder[1][1].real})
        denominator = (ratio-1)*(ratio+1)
        odd_targets = [first*ratio/denominator-arb(1)/2/span,
                       -second*ratio/denominator+arb(1)/2/span]
        for index, column in [(0, 1), (1, 0)]:
            projection_source = [odd['mixed'][row][index].conjugate() for row in range(2)]
            residual = odd_targets[index]-inverse_metric(projection_source, columns[column], odd)
            cuts[f'odd_jet_{index+1}'] = norm_square(residual)-odd['residual']*remainder[column][column].real
        even = geometry(theta, 'even')
        difference_column = [even_form[row][0]-even_form[row][1] for row in range(2)]
        cuts['even_value'] = inverse_norm(difference_column, even)-2*(even['norm']-even['kernel'].real)
        require_positive(even['residual'], 'even residual norm not positive on box for averaged jet division')
        even_targets = [first/denominator-opposite/span,
                        -second*ratio*ratio/denominator+endpoint/span]
        ones = [acb(1), acb(1)]
        coefficients = []
        for index, column in [(0, 1), (1, 0)]:
            fixed = [even_form[row][column]+(0 if even_shift is None else even_shift) for row in range(2)]
            projection_source = [even['mixed'][row][index].conjugate() for row in range(2)]
            slope = inverse_metric(projection_source, ones, even)
            residual = even_targets[index]-inverse_metric(projection_source, fixed, even)
            alpha = (inverse_norm(ones, even)+norm_square(slope)/even['residual'])/even['norm']
            beta = (inverse_metric(ones, fixed, even)
                    -slope.conjugate()*residual/even['residual'])/even['norm']
            gamma = (inverse_norm(fixed, even)+norm_square(residual)/even['residual'])/even['norm']
            coefficients.append((alpha, beta, gamma))
        alpha, beta, gamma = [sum(item[index] for item in coefficients)/2 for index in range(3)]
        require_positive(alpha, 'averaged even quadratic coefficient not positive')
        cuts['even_average_jet'] = (gamma-1)*alpha-norm_square(beta)
        cuts['even_average_normalized'] = gamma-norm_square(beta)/alpha-1
    except UnresolvedEnclosure as error:
        reason = str(error)
    for name in list(cuts):
        if not cuts[name].is_finite():
            del cuts[name]
            reason = 'one or more scalar cuts were nonfinite'
    return cuts, reason


def closed_ball(lower, upper):
    lower, upper = Fraction(lower), Fraction(upper)
    if not lower <= upper:
        raise ValueError('box endpoints are not ordered')
    midpoint_exact, radius_exact = (lower+upper)/2, (upper-lower)/2
    midpoint = arb(fmpq(midpoint_exact.numerator, midpoint_exact.denominator))
    radius = arb(fmpq(radius_exact.numerator, radius_exact.denominator))
    return arb(midpoint.mid(), (radius+midpoint.rad()).upper())


def evaluate_box(degree_bounds, coordinate_bounds, branch):
    theta = closed_ball(*degree_bounds)*arb.pi()/180
    logs = [acb(closed_ball(*coordinate_bounds[0]), closed_ball(*coordinate_bounds[1])),
            acb(closed_ball(*coordinate_bounds[2]), closed_ball(*coordinate_bounds[3]))]
    cuts, reason = necessary_cuts(theta, logs, branch)
    excluded = [name for name, value in cuts.items() if value > 0]
    return {'status': 'BOX_EXCLUDED' if excluded else 'INCOMPLETE', 'root_branch': branch,
            'reason': reason, 'exclusions': excluded,
            'cuts': {name: value.str(35, more=True) for name, value in cuts.items()}}


def decode_unit_ball(theta, variables):
    norm = (arb(1)/2).atanh()
    kernel = (complex_ball(0, theta/2).exp()/2).atanh()
    modulus_square = norm_square(kernel)
    require_positive(modulus_square, 'chart kernel modulus not bounded away from zero')
    modulus = modulus_square.sqrt()
    discriminant = norm*norm-modulus_square
    require_positive(discriminant, 'chart Gram determinant not positive on angle box')
    transverse = discriminant.sqrt()
    first, second = variables
    return [2*(kernel/modulus)*(norm*first+complex_ball(0, transverse)*second),
            2*(kernel.conjugate()/modulus)*(norm*first-complex_ball(0, transverse)*second)]


def cap_geometry(theta):
    norm = (arb(1)/2).atanh()
    kernel = (complex_ball(0, theta/2).exp()/2).atanh()
    modulus_square = norm_square(kernel)
    require_positive(modulus_square, 'chart kernel modulus not positive')
    modulus = modulus_square.sqrt()
    discriminant = norm*norm-modulus_square
    require_positive(discriminant, 'chart Gram determinant not positive on angle box')
    sigma_square = norm*norm-real_square(kernel.imag)
    require_positive(sigma_square, 'mean-log cap normal length not positive')
    sigma = sigma_square.sqrt()
    cosine_lower = 1-2*norm*norm+2*real_square(kernel.real)
    require_positive(cosine_lower, 'mean-log cosine lower bound not positive')
    even_norm = -(arb(3)/4).log()/2
    cap = ((arb(8)/9)*even_norm).log()/2-cosine_lower.log()
    normal_first = norm*kernel.real/modulus
    normal_second = -discriminant.sqrt()*kernel.imag/modulus
    return cap, sigma, normal_first, normal_second


def decode_cap_coordinates(theta, coordinates):
    cap, sigma, normal_first, normal_second = cap_geometry(theta)
    along, across, imaginary_first, imaginary_second = coordinates
    real_first = (normal_first*along-normal_second*across)/sigma
    real_second = (normal_second*along+normal_first*across)/sigma
    variables = [complex_ball(real_first, imaginary_first), complex_ball(real_second, imaginary_second)]
    return variables, cap


def unit_ball_cuts(theta, variables, branch, rayleigh=None, even_shift=None):
    cuts = {'unit4_ball': sum(norm_square(value) for value in variables)-1}
    if cuts['unit4_ball'] > 0:
        return cuts, None
    try:
        logs = decode_unit_ball(theta, variables)
    except UnresolvedEnclosure as error:
        return cuts, str(error)
    remaining, reason = necessary_cuts(theta, logs, branch, rayleigh=rayleigh, even_shift=even_shift)
    try:
        cap, _, _, _ = cap_geometry(theta)
        cuts['mean_log_cap'] = ((logs[0]+logs[1])/2).real-cap
    except UnresolvedEnclosure as error:
        return cuts, str(error)
    cuts.update(remaining)
    return cuts, reason


def tests():
    assert norm_square(acb(arb(0, '1e-30'), arb(0, '1e-30'))).is_finite()
    # Rational elementary certificate used by the logarithm-domain prefilters.
    upper = arb(7)/10
    assert 1+upper+upper**2/2+upper**3/6+upper**4/24 > 2
    argument = arb(7)/5
    assert 1-argument**2/2+argument**4/24-argument**6/720 > arb(1)/8
    for degree in [15, 30, 60, 90, 100]:
        theta = arb(degree)*arb.pi()/180
        endpoint = acb(0, theta/2).exp()/2
        root = acb(0, theta/4).exp()*(arb(1)/2).sqrt()
        for sign in [-1, 1]:
            logs = [2*sign*endpoint.atanh(), 2*sign*endpoint.conjugate().atanh()]
            ratio = (root/(1-sign*endpoint))/(root.conjugate()/(1-sign*endpoint.conjugate()))
            cuts, reason = necessary_cuts(theta, logs, ratio_override=ratio)
            assert reason is None, reason
            assert not any(value > 0 for value in cuts.values()), (degree, sign, cuts)
            norm, kernel = (arb(1)/2).atanh(), endpoint.atanh()
            modulus = norm_square(kernel).sqrt()
            decoded = decode_unit_ball(theta, [acb(sign*modulus/norm), acb(0)])
            assert all((actual-expected).contains(0) for actual, expected in zip(decoded, logs))
    outside, reason = unit_ball_cuts(arb(30)*arb.pi()/180, [acb(1), acb(1)], 1)
    assert outside['unit4_ball'] > 0 and reason is None
    theta = arb(32)*arb.pi()/180
    coordinates = [arb('-0.95'), arb('0.03'), arb('0.02'), arb('-0.01')]
    decoded, _ = decode_cap_coordinates(theta, coordinates)
    difference = sum(real_square(value) for value in coordinates)-sum(norm_square(value) for value in decoded)
    assert difference.contains(0), difference
    # All five necessary norm components at a noncolliding near-minimum screen point.
    coordinates = [('-1.0316401235514447',)*2, ('-0.33443970854443494',)*2,
                   ('-1.0316345023795823',)*2, ('0.33436638660311335',)*2]
    result = evaluate_box(('30', '30'), coordinates, 1)
    assert result['status'] == 'BOX_EXCLUDED'
    assert 'odd_PSD_determinant' in result['exclusions'] or 'even_average_jet' in result['exclusions']
    print('PASS: log sectors, ten Koebe controls/chart roundtrips, unit-ball cut, near-minimum exclusion')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', required=True, type=int)
    parser.add_argument('--test', action='store_true')
    parser.add_argument('--degree-bounds', nargs=2)
    parser.add_argument('--log-bounds', nargs=8)
    parser.add_argument('--branch', type=int, choices=[-1, 1])
    arguments = parser.parse_args()
    ctx.prec, ctx.threads = arguments.precision, 1
    if arguments.test:
        tests()
        return
    if arguments.degree_bounds is None or arguments.log_bounds is None or arguments.branch is None:
        parser.error('degree bounds, four complex-log coordinate intervals and branch are required')
    intervals = [arguments.log_bounds[index:index+2] for index in range(0, 8, 2)]
    print(json.dumps(evaluate_box(arguments.degree_bounds, intervals, arguments.branch), indent=2))


if __name__ == '__main__':
    main()
