#!/usr/bin/env python3
"""Validated centered cut and fixed-Rayleigh multiplier diagnostics.
Version 0.20 — Program B, 20261101__21:29 ET. Freeze and translate the even
quadratic near its minimizer before applying the validated mean-value form.
Local boxes only; all derivative domains must hold on the whole raw box.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time
import numpy as np
from flint import arb, acb, fmpq, ctx
from arb_differential import Differential, complex_ball
from fourlog_arb_box import decode_cap_coordinates, unit_ball_cuts, UnresolvedEnclosure
from fourlog_width_probe import center_for
from fourlog_global_probe import gram_data, screen


def rational_ball(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


def all_cuts(theta, coordinates, rayleigh, derivatives, even_shift=None):
    if derivatives:
        theta = Differential.variable(theta, 0)
        coordinates = [Differential.variable(value, index+1) for index, value in enumerate(coordinates)]
    variables, _ = decode_cap_coordinates(theta, coordinates)
    return unit_ball_cuts(theta, variables, 1, rayleigh=rayleigh, even_shift=even_shift)


def weighted(cuts, weight):
    if not all(name in cuts for name in ['odd_fixed_Rayleigh', 'even_average_normalized']):
        return None
    exact_weight = rational_ball(weight)
    return exact_weight*cuts['odd_fixed_Rayleigh']+(1-exact_weight)*cuts['even_average_normalized']


def frozen_vector(angle, point):
    geometry = gram_data(angle)
    _, _, auxiliary = screen(point, geometry, 1)
    logs = [complex(*point[:2]), complex(*point[2:])]
    cross = (auxiliary['mixed_logs'][0]-auxiliary['mixed_logs'][1])/2
    form = np.array([[logs[0]/2, cross], [cross, logs[1]/2]])
    inverse = geometry['odd']['coordinates_inverse']
    operator = inverse.T @ form @ inverse
    _, singular_values, right_vectors = np.linalg.svd(operator)
    endpoint_vector = inverse @ right_vectors.conj().T[:, 0]
    exact = [[Fraction(str(value.real)), Fraction(str(value.imag))] for value in endpoint_vector]
    vector = [acb(rational_ball(real), rational_ball(imag)) for real, imag in exact]
    shift = auxiliary['best_average_even_T']
    shift_exact = [Fraction(str(shift.real)), Fraction(str(shift.imag))]
    frozen_shift = acb(rational_ball(shift_exact[0]), rational_ball(shift_exact[1]))
    return vector, [[str(real), str(imag)] for real, imag in exact], singular_values.tolist(), frozen_shift


def fit_weight(angle, center, rayleigh, even_shift=None):
    theta = arb(angle)*arb.pi()/180
    cuts, reason = all_cuts(theta, [arb(value) for value in center], rayleigh, True, even_shift)
    if reason:
        raise ArithmeticError(reason)
    odd, even = [cuts[name] for name in ['odd_fixed_Rayleigh', 'even_average_normalized']]
    first = np.array([float(value.real) for value in odd.gradient[1:]])
    second = np.array([float(value.real) for value in even.gradient[1:]])
    difference = first-second
    optimum = min(1., max(0., -float(second @ difference)/float(difference @ difference)))
    weight = Fraction(optimum).limit_denominator(100000000)
    barrier = weighted(cuts, weight)
    return weight, {'central_value': barrier.value.real.str(35, more=True),
                    'theta_derivative': barrier.gradient[0].real.str(35, more=True),
                    'coordinate_gradient': [value.real.str(35, more=True) for value in barrier.gradient[1:]],
                    'maximum_coordinate_gradient': max(float(value.real.abs_upper()) for value in barrier.gradient[1:]),
                    'odd_squared_cut': odd.value.real.str(35, more=True),
                    'even_squared_cut': even.value.real.str(35, more=True)}


def local_bound(angle, center, radius, varying_angle, rayleigh, weight, mode, even_shift=None):
    width = rational_ball(radius)
    theta = arb(angle)*arb.pi()/180
    if varying_angle:
        theta += arb(0, width)
    coordinates = [arb(value, width) for value in center]
    radii = [theta.rad()]+[value.rad() for value in coordinates]
    try:
        ranges, _ = all_cuts(theta, coordinates, rayleigh, True, even_shift)
        centers, _ = all_cuts(theta.mid(), [value.mid() for value in coordinates], rayleigh, False, even_shift)
    except UnresolvedEnclosure:
        return None, None
    pairs = []
    if mode == 'barrier':
        range_barrier, center_barrier = weighted(ranges, weight), weighted(centers, weight)
        if range_barrier is not None and center_barrier is not None:
            pairs = [('fixed_positive_multiplier', range_barrier, center_barrier)]
    else:
        pairs = [(name, value, centers[name]) for name, value in ranges.items() if name in centers]
    best, reason = None, None
    for name, enclosure, central in pairs:
        if not enclosure.is_finite() or not central.is_finite():
            continue
        correction = sum((derivative.real.abs_upper()*halfwidth
                          for derivative, halfwidth in zip(enclosure.gradient, radii)), arb(0))
        mean_value = central-correction
        lower = max(enclosure.value.real.lower(), mean_value.lower())
        if best is None or lower > best:
            best, reason = lower, name
    return best, reason


def measure(angle, center, varying_angle, rayleigh, weight, mode, even_shift=None):
    lower, upper = Fraction(1, 2**28), Fraction(1, 16)
    value, _ = local_bound(angle, center, lower, varying_angle, rayleigh, weight, mode, even_shift)
    if value is None or not value > 0:
        return {'status': 'INCOMPLETE_AT_TINY_RADIUS'}
    for _ in range(20):
        middle = (lower+upper)/2
        value, _ = local_bound(angle, center, middle, varying_angle, rayleigh, weight, mode, even_shift)
        if value is not None and value > 0:
            lower = middle
        else:
            upper = middle
    value, cut = local_bound(angle, center, lower, varying_angle, rayleigh, weight, mode, even_shift)
    assert value is not None and value > 0
    return {'status': 'VALIDATED_LOCAL_EXCLUSION_ONLY', 'excluded_halfwidth': float(lower),
            'excluded_halfwidth_exact': str(lower), 'unresolved_halfwidth': float(upper),
            'lower_bound': value.str(35, more=True), 'cut': cut}


def derivative_test():
    point, center = center_for(30)
    rayleigh, _, _, even_shift = frozen_vector(30, point)
    theta = arb(30)*arb.pi()/180
    cuts, reason = all_cuts(theta, [arb(value) for value in center], rayleigh, True, even_shift)
    assert reason is None
    unshifted, _ = all_cuts(theta, [arb(value) for value in center], rayleigh, True)
    delta = cuts['even_average_normalized']-unshifted['even_average_normalized']
    assert delta.value.contains(0) and all(item.contains(0) for item in delta.gradient)
    step = arb((1, -35))
    for dimension in range(5):
        positive, negative = [arb(value) for value in center], [arb(value) for value in center]
        theta_positive, theta_negative = theta, theta
        if dimension == 0:
            theta_positive, theta_negative = theta+step, theta-step
        else:
            positive[dimension-1] += step
            negative[dimension-1] -= step
        first, _ = all_cuts(theta_positive, positive, rayleigh, False, even_shift)
        second, _ = all_cuts(theta_negative, negative, rayleigh, False, even_shift)
        for name in ['odd_cross_log_disk', 'odd_fixed_Rayleigh', 'even_average_normalized']:
            difference = cuts[name].gradient[dimension].real-(first[name]-second[name])/(2*step)
            assert difference.abs_upper() < arb('1e-8'), (dimension, name, difference)
    print('PASS: all five real derivatives of three smooth cuts against high-precision central differences')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, required=True)
    parser.add_argument('--test', action='store_true')
    parser.add_argument('--angles', type=int, nargs='+')
    parser.add_argument('--output', type=Path)
    arguments = parser.parse_args()
    ctx.prec, ctx.threads = arguments.precision, 1
    if arguments.test:
        derivative_test()
        return
    if arguments.output is None or arguments.angles is None:
        parser.error('--angles and --output required outside --test')
    started = time.process_time()
    rows = []
    for angle in arguments.angles:
        point, center = center_for(angle)
        rayleigh, exact, singular_values, even_shift = frozen_vector(angle, point)
        weight, central = fit_weight(angle, center, rayleigh, even_shift)
        for mode in ['individual', 'barrier']:
            for varying in [False, True]:
                row = measure(angle, center, varying, rayleigh, weight, mode, even_shift)
                row.update(angle_degrees=angle, mode=mode, angle_radius_in_radians=varying,
                           rational_weight=str(weight), rayleigh=exact, singular_values=singular_values,
                           central_diagnostic=central, cap_center=[str(Fraction.from_float(value)) for value in center])
                row['frozen_even_shift'] = [even_shift.real.str(40, more=True), even_shift.imag.str(40, more=True)]
                rows.append(row)
    output = {'status': 'CENTERED_LOCAL_BOXES_NOT_A_GLOBAL_CERTIFICATE',
              'cpu_seconds': time.process_time()-started, 'rows': rows}
    arguments.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({'cpu_seconds': output['cpu_seconds'], 'rows': [{key: row.get(key) for key in
        ['angle_degrees', 'mode', 'angle_radius_in_radians', 'excluded_halfwidth', 'rational_weight', 'cut']}
        for row in rows]}, indent=2))


if __name__ == '__main__':
    main()
