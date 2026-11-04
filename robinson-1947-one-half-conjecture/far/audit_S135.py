#!/usr/bin/env python3
# audit_S135.py — third independent check (audit) of program a's S135 proof (Robinson 1947)
# version 0.10 — audit, 20261101_2010 ET — own interval arithmetic (mpmath 60 digits, outward padding) + exact Sturm counts
"""Independent of check_sector135.py:
 (A) mixed term: my OWN adaptive c-cover proves the fixed-phase polarization sum < 173/250 on c in [0, 383/1000];
 (B) ball step: for each of the author's 11 c-cells I re-enclose a, b, beta (my interval code, 64 subcells) and check the
     author's rational a+, b+, beta+ dominate; then N(t) > 0 on [0,1] by exact Sturm count (sympy), not Bernstein;
 (C) scalars: sin(pi/8) < 383/1000, root/endpoint comparisons for Re e^W > 277/800 with exact Taylor bounds;
 (D) numeric sanity: formula (8) vs complex evaluation; Koebe rotations in the sector."""
import json, math, os
from fractions import Fraction as Fr
import mpmath as mp
import sympy as sp

mp.mp.dps = 60
PAD = mp.mpf('1e-45')
CERT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'S135_certificate.json')


class Iv:
    """closed interval [lo, hi] with mpf endpoints; monotone functions evaluated at endpoints and padded outward."""
    def __init__(self, lo, hi=None):
        self.lo, self.hi = mp.mpf(lo), mp.mpf(hi if hi is not None else lo)
        assert self.lo <= self.hi

    def __add__(self, o): o = as_iv(o); return Iv(self.lo + o.lo - PAD, self.hi + o.hi + PAD)
    def __radd__(self, o): return self + o
    def __sub__(self, o): o = as_iv(o); return Iv(self.lo - o.hi - PAD, self.hi - o.lo + PAD)
    def __rsub__(self, o): return as_iv(o) - self
    def __neg__(self): return Iv(-self.hi, -self.lo)

    def __mul__(self, o):
        o = as_iv(o)
        prods = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return Iv(min(prods) - PAD, max(prods) + PAD)
    def __rmul__(self, o): return self * o

    def __truediv__(self, o):
        o = as_iv(o)
        assert o.lo > 0 or o.hi < 0
        return self * Iv(1 / o.hi - PAD, 1 / o.lo + PAD)


def as_iv(x): return x if isinstance(x, Iv) else Iv(x)
def iv_inc(fn, x): return Iv(fn(x.lo) - PAD, fn(x.hi) + PAD)          # increasing function
def iv_sqrt(x): return iv_inc(mp.sqrt, Iv(max(x.lo, 0), x.hi))
def iv_log(x): return iv_inc(mp.log, x)
def iv_atan(x): return iv_inc(mp.atan, x)
def iv_atanh(x): return iv_inc(mp.atanh, x)


# ---------- (A) mixed term ----------
def mixed_upper(c_iv):
    x = mp.mpf(1) / 4
    k = 1 - 2 * c_iv * c_iv
    s = 2 * c_iv * iv_sqrt(1 - c_iv * c_iv)
    D = 1 + 2 * x * k + x * x
    A0 = -x * (1 + 2 * x * k + x * x * (2 * k * k - 1)) / (D * D)
    J = iv_atan(x * s / (1 + x * k))
    B0 = -(k / 2) * iv_log(D) - s * J
    U0, V0 = Iv(mp.mpf(4) / 9), Iv(mp.log(mp.mpf(4) / 3) - PAD, mp.log(mp.mpf(4) / 3) + PAD)
    return iv_sqrt((U0 + A0) * (V0 + B0)).hi + iv_sqrt((U0 - A0) * (V0 - B0)).hi


def check_mixed():
    bound = mp.mpf(173) / 250
    stack, cells, worst = [(mp.mpf(0), mp.mpf(383) / 1000, 0)], 0, mp.mpf(0)
    while stack:
        lo, hi, depth = stack.pop()
        up = mixed_upper(Iv(lo, hi))
        if up < bound:
            cells += 1
            worst = max(worst, up)
            continue
        assert depth < 40, (lo, hi, up)
        mid = (lo + hi) / 2
        stack += [(lo, mid, depth + 1), (mid, hi, depth + 1)]
    print(f"(A) mixed term: {cells} cells, max upper {mp.nstr(worst, 12)} < 173/250 = .692 : PASS")


# ---------- (B) ball step ----------
def abb_enclosure(c_iv):
    R = Iv(mp.log(3) - PAD, mp.log(3) + PAD)
    u = iv_atanh(4 * c_iv / 5) / 2
    v = iv_atan(mp.mpf(4) / 3 * iv_sqrt(1 - c_iv * c_iv)) / 2
    beta = iv_sqrt(R * R - 4 * u * u)
    a = 4 * u * v / beta
    b = R * iv_sqrt(R * R - 4 * u * u - 4 * v * v) / beta
    return a.hi, b.hi, beta.hi


def sturm_positive(a_p, b_p, beta_p, T):
    t = sp.symbols('t')
    den = 1 + t ** 2
    un = T * den - a_p * (1 - t ** 2) - 2 * b_p * t
    dn = beta_p * (1 - t ** 2)
    en = sum(un ** j * den ** (8 - j) / sp.factorial(j) for j in range(9))
    co = den ** 6 - dn ** 2 * den ** 4 / 2 + dn ** 4 * den ** 2 / 24 - dn ** 6 / 720
    poly = sp.Poly(sp.expand(en * co - den ** 14), t)
    return poly.count_roots(0, 1) == 0 and poly.eval(0) > 0


def check_ball(cert):
    T = sp.Rational(211, 200)
    covered = Fr(0)
    for cell in cert['ball_cover']:
        c_lo, c_hi = Fr(cell['c'][0]), Fr(cell['c'][1])
        assert c_lo == covered, "cover must be contiguous"
        covered = c_hi
        a_p, b_p, beta_p = (sp.Rational(x) for x in cell['a_b_beta'])
        sub = 64
        width = (c_hi - c_lo) / sub
        maxima = [mp.mpf(0)] * 3
        for j in range(sub):
            lo_f, hi_f = c_lo + j * width, c_lo + (j + 1) * width
            enc = abb_enclosure(Iv(mp.mpf(lo_f.numerator) / lo_f.denominator, mp.mpf(hi_f.numerator) / hi_f.denominator))
            maxima = [max(m, e) for m, e in zip(maxima, enc)]
        consts = [mp.mpf(Fr(x).numerator) / Fr(x).denominator for x in cell['a_b_beta']]
        assert all(m <= cst for m, cst in zip(maxima, consts)), (cell['c'], maxima, consts)
        assert beta_p < sp.Rational(6, 5) and a_p + b_p < T
        assert sturm_positive(a_p, b_p, beta_p, T), cell['c']
    assert covered == Fr(383, 1000)
    print(f"(B) ball step: {len(cert['ball_cover'])} cells; author's a+,b+,beta+ dominate my enclosures; N>0 by Sturm: PASS")


# ---------- (C) scalars ----------
def exp_lower(x, terms): return sum(x ** j / math.factorial(j) for j in range(terms + 1))
def exp_upper12(x): return exp_lower(x, 12) + x ** 13 / math.factorial(13) / (1 - x / 14)


def check_scalars():
    T = Fr(211, 200)
    pi_up = Fr(22, 7)
    xx = pi_up / 8
    sin_up = xx - xx ** 3 / 6 + xx ** 5 / 120                      # sin x <= degree-5 sum for 0 <= x <= pi
    assert sin_up < Fr(383, 1000)
    y = Fr(57, 100)
    assert T * (y - y ** 3 / 6 + y ** 5 / 120) < y                  # T sin(.57) < .57
    assert 1 - y ** 2 / 2 + y ** 4 / 24 - y ** 6 / 720 > Fr(21, 25)  # cos(.57) > .84
    assert exp_upper12(T * Fr(21, 25)) < Fr(672, 277) and exp_upper12(T) < Fr(800, 277)
    assert Fr(21, 25) * Fr(277, 672) == Fr(277, 800)
    assert Fr(277, 400) - Fr(173, 250) == Fr(1, 2000)
    print("(C) scalars: PASS")


# ---------- (D) numeric sanity ----------
def check_numeric():
    x = 0.25
    for eps in [0.01, 0.3, 0.7, 1.1]:
        k, s = math.cos(eps), math.sin(eps)
        zeta = x * complex(math.cos(eps), -math.sin(eps))
        a_cx = (-x / (1 + zeta) ** 2).real
        b_cx = (-complex(math.cos(eps), math.sin(eps)) * complex(math.log(abs(1 + zeta)), math.atan2((1 + zeta).imag, (1 + zeta).real))).real
        D = 1 + 2 * x * k + x * x
        a_f = -x * (1 + 2 * x * k + x * x * (2 * k * k - 1)) / D ** 2
        b_f = -(k / 2) * math.log(D) - s * math.atan(x * s / (1 + x * k))
        assert abs(a_cx - a_f) < 1e-14 and abs(b_cx - b_f) < 1e-14
    worst = 10.0
    for rot_idx in range(720):
        phi = 2 * math.pi * rot_idx / 720
        rot = complex(math.cos(phi), math.sin(phi))
        for th_idx in range(46):
            theta = math.radians(135 + th_idx)
            zz = 0.5 * complex(math.cos(theta / 2), math.sin(theta / 2))
            ww = zz.conjugate()
            fz, fw = (rot * zz) / (1 - rot * zz) ** 2, (rot * ww) / (1 - rot * ww) ** 2
            dz, dw = rot * (1 + rot * zz) / (1 - rot * zz) ** 3, rot * (1 + rot * ww) / (1 - rot * ww) ** 3
            worst = min(worst, (1 + (zz * dz - ww * dw) / (fz - fw)).real)
    print(f"(D) formula (8) matches complex form; Koebe rotations 135-180 deg min Re Q = {worst:.6f}: PASS")
    assert worst > 1 / 2000


def main():
    cert = json.load(open(CERT))
    check_scalars()
    check_numeric()
    check_mixed()
    check_ball(cert)
    print("S135 AUDIT PASS")


if __name__ == "__main__":
    main()
