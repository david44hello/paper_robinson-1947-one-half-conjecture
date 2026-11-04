#!/usr/bin/env python3
"""Independent Arb AD2 arithmetic for generic HOLQ support.
Version 0.40 — Program B, 20261102__09:51 EST. Add a reviewer's direct actual-f
joint-modulus assertion to the42 trusted-program controls; arithmetic unchanged.
"""
import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time
from flint import arb, acb, ctx
from arb_differential import SecondDifferential
from fourlog_arb_box import closed_ball, norm_square, real_square, require_positive, UnresolvedEnclosure
from fourlog_centered import rational_ball
from holq_local_arb import cosine, sine, exact_intersection, quotient as plain_quotient
from holq_joint_cap_arb import JointCap


@dataclass(frozen=True)
class Support:
    weight_u: Fraction
    weight_s: Fraction
    kind: str
    cap_packet: object = None

    def __post_init__(self):
        if self.weight_u < 0 or self.weight_s < 0:
            raise ValueError('support weights must be nonnegative exact rationals')
        if self.kind == 'EVEN_VALUE':
            if self.weight_s != 0 or self.cap_packet is not None:
                raise ValueError('EVEN_VALUE requires mu=0 and no joint packet')
        elif self.kind == 'JOINT_P55':
            if self.weight_u != Fraction(4, 5) or self.weight_s != Fraction(1, 2) or not isinstance(self.cap_packet, JointCap):
                raise ValueError('JOINT_P55 requires lambda4/5,mu1/2 and verified exact canonical P55 packet')
        else:
            raise ValueError('unsupported support cap kind')

    def tokens(self):
        return [str(self.weight_u), str(self.weight_s), self.kind]


def tangent(theta):
    denominator = cosine(theta/4).real
    require_positive(denominator, 'positive tan denominator required')
    result = sine(theta/4).real/denominator
    require_positive(result, 'strictly positive angle required')
    return result


def forms(balls):
    SecondDifferential.set_box([arb(0, value.rad()) for value in balls]+[arb(0)])
    alpha, psi, omega, theta = [SecondDifferential.variable(value, index) for index, value in enumerate(balls)]
    norm = (arb(1)/2).atanh()
    kernel = ((acb(0, 1)*theta/2).exp()/2).atanh()
    first_square = (norm+kernel.real)/2
    require_positive(first_square, 'first Gram length unresolved')
    first = first_square.sqrt()
    cross = kernel.imag/(2*first)
    determinant = norm*norm-norm_square(kernel)
    require_positive(determinant, 'Gram determinant unresolved')
    last_square = determinant/(2*(norm+kernel.real))
    require_positive(last_square, 'second Gram length unresolved')
    last = last_square.sqrt()
    cos_alpha, sin_alpha = cosine(alpha).real, sine(alpha).real
    diagonal_one = cos_alpha*(acb(0, 1)*(psi+omega)).exp()
    off_diagonal = acb(0, 1)*sin_alpha*(acb(0, 1)*psi).exp()
    diagonal_two = cos_alpha*(acb(0, 1)*(psi-omega)).exp()
    uu = first_square*diagonal_one
    vv = real_square(cross)*diagonal_one+2*cross*last*off_diagonal+last_square*diagonal_two
    ww = first*cross*diagonal_one+first*last*off_diagonal
    return theta, uu, vv, ww


def support_u_value(theta, uu, vv, ww):
    tau = tangent(theta)
    chi = acb(0, 1)*tau*(2*(uu+vv)).exp()
    plus, minus = 1+chi, 1-chi
    require_positive(plus.imag, 'Log(1+chi) upper half-plane unresolved')
    require_positive(-minus.imag, 'Log(1-chi) lower half-plane unresolved')
    delta = acb(0, 1)*theta/2-plus.log()+minus.log()
    support_u = delta+acb(0, 4)*ww
    return support_u, chi


def even_cap(theta):
    endpoint = (acb(0, 1)*theta/2).exp()/2
    even_kernel = -(1-endpoint*endpoint).log()/2
    even_norm = -(arb(3)/4).log()/2
    radicand = even_norm*even_norm-real_square(even_kernel.real)
    require_positive(radicand, 'even support cap square-root unresolved')
    cap = 2*radicand.sqrt()
    return cap


def support_u_cap(theta, uu, vv, ww):
    support_u, chi = support_u_value(theta, uu, vv, ww)
    return support_u, even_cap(theta), chi


def quotient_from_forms(theta, uu, vv, ww, support):
    tau = tangent(theta)
    ell_one, ell_two = 2*(uu-vv)+acb(0, 4)*ww, 2*(uu-vv)-acb(0, 4)*ww
    first, second = ell_one.exp(), ell_two.exp()
    cross = 2*(uu+vv)
    original = 1+(first+second)/2+(first-second)*acb(0, 1)*(tau*cross.exp()-(-cross).exp()/tau)/4
    normal = 1+(2*(uu-vv)).exp()*cosine(4*ww)
    normal += ((-4*vv).exp()/tau-tau*(4*uu).exp())*sine(4*ww)/2
    if isinstance(original, SecondDifferential):
        quotient = exact_intersection(original, normal)
    else:
        quotient = acb(original.real.intersection(normal.real), original.imag.intersection(normal.imag))
    if support.weight_u == 0 and support.weight_s == 0:
        return quotient.real
    support_u, _ = support_u_value(theta, uu, vv, ww)
    support_s = first+second-quotient
    # Csup=lambda*Ce, NOT bare Ce: normalization is tied to exact weights.
    cap_total = (rational_ball(support.weight_u)*even_cap(theta) if support.kind == 'EVEN_VALUE'
                 else support.cap_packet.evaluate(theta))
    return (quotient+rational_ball(support.weight_u)*acb(0, 1)*support_u
            +rational_ball(support.weight_s)*support_s-cap_total).real


def quotient(balls, support):
    return quotient_from_forms(*forms(balls), support)


def check_endpoints(endpoints, support, target):
    balls = [closed_ball(*interval) for interval in endpoints]
    ranges = quotient(balls, support)
    center = quotient([value.mid() for value in balls], support)
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
    lower = max(ranges.value.real.lower(), (center.value.real-linear-absolute).lower(),
                (center.value.real-linear-signed).lower())
    return {'status': 'INDEPENDENT_LOCAL_BOX_CONFIRMED' if lower > rational_ball(target) else 'INCOMPLETE',
            'lower': lower.str(35, more=True), 'target_exact': str(target), 'support': support.tokens(),
            'endpoints_exact': [[str(a), str(b)] for a, b in endpoints]}


def compare(actual, expected):
    if not (actual-expected).contains(0):
        raise AssertionError(f'normalization disagreement: {actual} versus {expected}')


def actual_family_case(theta, log_f_z, log_f_w, p_z, p_w, support):
    endpoint = (acb(0, theta/2)).exp()/2
    other = endpoint.conjugate()
    first_value, second_value = endpoint*log_f_z.exp(), other*log_f_w.exp()
    hs = endpoint.sqrt()*(log_f_z/2).exp()
    ht = other.sqrt()*(log_f_w/2).exp()
    ratio = hs/ht
    chi = (ratio-1)/(ratio+1)
    cross = (chi/acb(0, tangent(theta))).log()/2
    ell_one, ell_two = p_z.log(), p_w.log()
    difference = (ell_one+ell_two)/4
    uu, vv, ww = (cross+difference)/2, (cross-difference)/2, (ell_one-ell_two)/acb(0, 8)
    support_u, cap, _ = support_u_cap(theta, uu, vv, ww)
    direct_u = (log_f_w-log_f_z)/2+(ell_one-ell_two)/2
    compare(support_u, direct_u)
    if not support_u.abs_upper() <= cap.lower():
        raise AssertionError('actual-family even support bound not confirmed')
    direct_q = 1+(p_z*first_value-p_w*second_value)/(first_value-second_value)
    direct_s = p_z+p_w-direct_q
    cap_total = rational_ball(support.weight_u)*cap if support.kind == 'EVEN_VALUE' else support.cap_packet.evaluate(theta)
    if support.kind == 'JOINT_P55':
        direct_weighted = rational_ball(support.weight_u)*acb(0, 1)*direct_u+rational_ball(support.weight_s)*direct_s
        if not direct_weighted.abs_upper() <= cap_total.lower():
            raise AssertionError('direct actual-function joint support modulus bound not confirmed')
    expected = (direct_q+rational_ball(support.weight_u)*acb(0, 1)*direct_u
                +rational_ball(support.weight_s)*direct_s-cap_total).real
    compare(quotient_from_forms(theta, uu, vv, ww, support), expected)


def tests(support):
    count = 0
    for degree in [30, 55, 65, 90, 120, 170]:
        theta = arb(degree)*arb.pi()/180
        endpoint = (acb(0, theta/2)).exp()/2
        other = endpoint.conjugate()
        for coefficient in [acb(0), acb('0.5'), acb('-0.5'), acb(1), acb(-1), acb(0, arb('0.4')).exp()]:
            log_z, log_w = -2*(1-coefficient*endpoint).log(), -2*(1-coefficient*other).log()
            p_z, p_w = (1+coefficient*endpoint)/(1-coefficient*endpoint), (1+coefficient*other)/(1-coefficient*other)
            actual_family_case(theta, log_z, log_w, p_z, p_w, support)
            count += 1
    for degree in [55, 70, 100]:
        theta = arb(degree)*arb.pi()/180
        endpoint = (acb(0, theta/2)).exp()/2
        other = endpoint.conjugate()
        first, second = acb(0, arb('0.3')).exp(), acb(0, arb('-1.1')).exp()
        for mixture in [arb(1)/3, arb(1)]:
            def values(point):
                logarithm = -2*mixture*(1-first*point).log()-2*(1-mixture)*(1-second*point).log()
                pre_schwarz = 1+2*mixture*first*point/(1-first*point)+2*(1-mixture)*second*point/(1-second*point)
                return logarithm, pre_schwarz
            log_z, p_z = values(endpoint)
            log_w, p_w = values(other)
            actual_family_case(theta, log_z, log_w, p_z, p_w, support)
            count += 1
    balls = [arb('.6', '.0001'), arb('.7', '.0001'), arb('-.4', '.0001'), arb('1.2', '.0001')]
    zero = Support(Fraction(0), Fraction(0), 'EVEN_VALUE')
    exact_intersection(SecondDifferential.lift(quotient(balls, zero)), plain_quotient(balls))
    theta, uu, vv, ww = forms(balls)
    support_u, _, chi = support_u_cap(theta, uu, vv, ww)
    ratio = (1+chi)/(1-chi)
    require_positive(ratio.imag, 'test ratio upper half-plane')
    alternate = acb(0, 1)*theta/2-ratio.log()+acb(0, 4)*ww
    exact_intersection(support_u, alternate)
    try:
        support_u_cap(arb(1), acb(0, 1), acb(0), acb(0))
    except UnresolvedEnclosure:
        pass
    else:
        raise AssertionError('wrong Log half-plane was accepted')
    endpoints = [[Fraction('.599'), Fraction('.601')], [Fraction('.699'), Fraction('.701')],
                 [Fraction('-.401'), Fraction('-.399')], [Fraction('1.1334'), Fraction('1.1354')]]
    local = check_endpoints(endpoints, support, Fraction(0))
    if local['status'] != 'INDEPENDENT_LOCAL_BOX_CONFIRMED':
        raise AssertionError('positive local support-box control did not confirm')
    for invalid in [(Fraction(-1), Fraction(0), 'EVEN_VALUE'),
                    (Fraction(1), Fraction(1), 'EVEN_VALUE'), (Fraction(1), Fraction(0), 'JOINT')]:
        try:
            Support(*invalid)
        except ValueError:
            continue
        raise AssertionError('invalid support accepted')
    return {'test': 'PASS', 'actual_function_cases': count, 'local_box': local,
            'controls': ['36 Koebe/identity/interior-family cases', '6 extreme-starlike cases',
                         'lambda0 value/gradient/all25Hessian comparison with plain HOLQ',
                         'two U branch forms value/gradient/all25Hessian', 'invalid weights/kinds rejected',
                         'wrong logarithm half-plane rejected', 'real rectangular local box confirmed']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, required=True)
    parser.add_argument('--support', nargs=3, required=True)
    parser.add_argument('--cap-packet', type=Path)
    parser.add_argument('--test', action='store_true', required=True)
    parser.add_argument('--output', type=Path, required=True)
    arguments = parser.parse_args()
    ctx.prec, ctx.threads = arguments.precision, 1
    packet = JointCap.from_file(arguments.cap_packet) if arguments.cap_packet is not None else None
    support = Support(Fraction(arguments.support[0]), Fraction(arguments.support[1]), arguments.support[2], packet)
    started = time.process_time()
    result = tests(support)
    result.update(support=support.tokens(), cpu_seconds=time.process_time()-started,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    arguments.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
