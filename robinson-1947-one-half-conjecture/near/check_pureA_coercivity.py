#!/usr/bin/env python3
"""Exact model-coercivity polynomial probe, program a.
Version 0.20. Rational tensor Bernstein certificate; PASS only on an exact check.
"""
import argparse
from fractions import Fraction as F
from math import comb
import sympy as sp


def bernstein2(poly,variables,bounds):
    deg=[poly.degree(item) for item in variables]
    transformed={}
    for powers,coefficient in poly.terms():
        coefficient=F(coefficient)
        for first in range(powers[0]+1):
            aa=F(comb(powers[0],first))*bounds[0][0]**(powers[0]-first)*(bounds[0][1]-bounds[0][0])**first
            for second in range(powers[1]+1):
                bb=F(comb(powers[1],second))*bounds[1][0]**(powers[1]-second)*(bounds[1][1]-bounds[1][0])**second
                transformed[first,second]=transformed.get((first,second),F(0))+coefficient*aa*bb
    output=[]
    for row in range(deg[0]+1):
        for column in range(deg[1]+1):
            value=sum((transformed.get((ii,jj),F(0))*F(comb(row,ii),comb(deg[0],ii))*F(comb(column,jj),comb(deg[1],jj))
                       for ii in range(row+1) for jj in range(column+1)),F(0))
            output.append(value)
    return min(output),deg,len(output)


def run_probe(kappa):
    tt,cc,xx=sp.symbols('t c x')
    vv=1-tt**2;ss=sp.Rational(1,4)-tt**2;dd=cc-tt
    nlocal=vv*(6*dd**2+8*tt*dd)-4*tt*dd**3-6*tt**2*dd**2
    numerator=sp.Poly(vv*(2*(1-2*tt*cc)*vv**2-ss*nlocal),cc)
    denominator=sp.Poly((vv**2+dd**2*ss)*(vv**2-(cc**2-tt**2)*ss),cc)
    ncoef=[sp.Poly(numerator.nth(ii),tt,xx) for ii in range(numerator.degree()+1)]
    dcoef=[sp.Poly(denominator.nth(ii),tt,xx) for ii in range(denominator.degree()+1)]
    cheb=[sp.Poly(sp.chebyshevt(ii,xx),tt,xx) for ii in range(5)]
    real_num=sp.Poly(0,tt,xx);den_square=sp.Poly(0,tt,xx)
    for ii,first in enumerate(ncoef):
        for jj,second in enumerate(dcoef):real_num+=first*second*cheb[abs(ii-jj)]
    for ii,first in enumerate(dcoef):
        for jj,second in enumerate(dcoef):den_square+=first*second*cheb[abs(ii-jj)]
    qnum=sp.Rational(1,2)-tt;qden=sp.Rational(3,4)*(sp.Rational(5,4)+2*tt)
    difference=sp.Poly(qden,tt,xx)*real_num-sp.Poly(qnum,tt,xx)*den_square
    divided,remainder=sp.div(sp.Poly(difference.as_expr(),xx),sp.Poly(1-xx,xx))
    assert remainder.is_zero
    target=sp.Poly(divided.as_expr(),tt,xx)-sp.Poly(sp.Rational(kappa.numerator,kappa.denominator)*qden,tt,xx)*den_square
    minimum,degrees,count=bernstein2(target,(tt,xx),[(F(19,40),F(1,2)),(F(-1),F(1))])
    print('degrees',degrees,'coefficients',count,'minimum',minimum,'decimal',float(minimum),flush=True)
    assert minimum>0,'No global polynomial positivity certificate at this kappa'
    print('PASS: exact model Re Q_c >= Q_K + '+str(kappa)+'*(1-Re c) for all |c|<=1,19/40<=t<=1/2',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--test',required=True,action='store_true')
    parser.add_argument('--kappa',required=True,type=F)
    args=parser.parse_args()
    run_probe(args.kappa)
