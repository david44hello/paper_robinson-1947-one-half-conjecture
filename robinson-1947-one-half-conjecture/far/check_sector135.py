#!/usr/bin/env python3
"""S135 rational interval and Bernstein certificate, program a.
Version 0.20 — 20261101__20:01 ET. Intersect interval products with known squared-norm nonnegativity before taking roots; uniform c-cover for BALL and phase polarization.
"""
import argparse
from fractions import Fraction as F
from math import comb, factorial, isqrt, sin, cos, log, pi
from pathlib import Path
import json
from check_sector165 import add, mul, power, scale, split, lower_exp, upper_exp

SCALE=10**10


def rounded(interval):
    low,high=interval
    return (F((low*SCALE).__floor__(),SCALE),F((high*SCALE).__ceil__(),SCALE))


def plus(first,second):
    return first[0]+second[0],first[1]+second[1]


def times(first,second):
    values=[x*y for x in first for y in second]
    return min(values),max(values)


def divide(first,second):
    assert second[0]>0
    return times(first,(1/second[1],1/second[0]))


def const(value):
    return F(value),F(value)


def neg(interval):
    return -interval[1],-interval[0]


def square(interval):
    low,high=interval
    return (F(0) if low<=0<=high else min(low*low,high*high),max(low*low,high*high))


def sqrt_interval(interval):
    low,high=interval
    assert low>=0
    ilo=isqrt(low.numerator*SCALE*SCALE//low.denominator)
    ihi=isqrt(high.numerator*SCALE*SCALE//high.denominator)
    return F(ilo,SCALE),F(ihi+1,SCALE)


def atanh_point(value):
    assert 0<=value<=F(1,2)
    total=sum((value**(2*j+1)/F(2*j+1) for j in range(32)),F(0))
    return rounded((total,total+value**65/(65*(1-value*value))))


def atanh_interval(interval):
    return atanh_point(interval[0])[0],atanh_point(interval[1])[1]


def atan_small(value):
    assert 0<=value<=F(1,2)
    lower=sum(((-1)**j*value**(2*j+1)/F(2*j+1) for j in range(16)),F(0))
    return rounded((lower,lower+value**33/33))


def pi_interval():
    return plus(times(const(16),atan_small(F(1,5))),times(const(-4),atan_small(F(1,239))))


def atan_point(value):
    if value<=F(1,2):
        return atan_small(value)
    assert 1<=value<=F(3,2)
    residual=(value-1)/(value+1)
    return plus(times(const(F(1,4)),pi_interval()),atan_small(residual))


def atan_interval(interval):
    return rounded((atan_point(interval[0])[0],atan_point(interval[1])[1]))


def log_interval(interval):
    assert interval[0]>=1
    argument=divide(plus(interval,const(-1)),plus(interval,const(1)))
    return times(const(2),atanh_interval(argument))


def ball_constants(c_interval):
    real_z=times(const(F(1,2)),atanh_interval(times(const(F(4,5)),c_interval)))
    sine_half=sqrt_interval(plus(const(1),neg(square(c_interval))))
    imag_z=times(const(F(1,2)),atan_interval(times(const(F(4,3)),sine_half)))
    radius=times(const(2),atanh_point(F(1,2)))
    beta=sqrt_interval(plus(square(radius),neg(times(const(4),square(real_z)))))
    alpha=divide(times(const(4),times(real_z,imag_z)),beta)
    delta=sqrt_interval(plus(square(radius),neg(times(const(4),plus(square(real_z),square(imag_z))))))
    bravo=divide(times(radius,delta),beta)
    # Round outward to short decimal fractions before degree-28 arithmetic.
    uppers=[]
    for interval in [alpha,bravo,beta]:
        uppers.append(F((interval[1]*10**7).__ceil__(),10**7))
    return tuple(uppers)


def polynomial(alpha,bravo,beta):
    den=[F(1),F(0),F(1)]
    unum=add(scale(den,F(211,200)),[-alpha,-2*bravo,alpha])
    dnum=[beta,F(0),-beta]
    exponential=[F(0)]
    for index in range(9):
        exponential=add(exponential,scale(mul(power(unum,index),power(den,8-index)),F(1,factorial(index))))
    cosine=power(den,6)
    for index,coefficient in [(2,-F(1,2)),(4,F(1,24)),(6,-F(1,720))]:
        cosine=add(cosine,scale(mul(power(dnum,index),power(den,6-index)),coefficient))
    result=add(mul(exponential,cosine),scale(power(den,14),-1))
    return [sum((result[index]*F(comb(degree,index),comb(28,index)) for index in range(degree+1)),F(0)) for degree in range(29)]


def bernstein_cover(coefficients,depth=0):
    if min(coefficients)>0:
        return [(depth,min(coefficients))]
    if depth>=7 or coefficients[0]<=0 or coefficients[-1]<=0:
        return None
    left,right=split(coefficients)
    first=bernstein_cover(left,depth+1)
    if first is None:
        return None
    second=bernstein_cover(right,depth+1)
    return None if second is None else first+second


def ball_cover(low,high,depth=0):
    alpha,bravo,beta=ball_constants((low,high))
    # Samples only choose subdivision; all accepted cells need exact positivity.
    sampled=max(float(alpha)*cos(index*pi/128)+float(bravo)*sin(index*pi/128)
                -log(cos(float(beta)*cos(index*pi/128))) for index in range(65))
    certificate=None
    if sampled<1.055-1e-7 and alpha+bravo<F(211,200) and beta<F(6,5):
        certificate=bernstein_cover(polynomial(alpha,bravo,beta))
    if certificate is not None:
        return [{'c':[str(low),str(high)],'a_b_beta':list(map(str,[alpha,bravo,beta])),
                 't_depths':[item[0] for item in certificate],
                 'minimum_bernstein':str(min(item[1] for item in certificate))}]
    assert depth<14,'BALL cover failed'
    middle=(low+high)/2
    return ball_cover(low,middle,depth+1)+ball_cover(middle,high,depth+1)


def mixed_upper(c_interval):
    cosine=plus(const(1),neg(times(const(2),square(c_interval))))
    sine=times(times(const(2),c_interval),sqrt_interval(plus(const(1),neg(square(c_interval)))))
    xx=F(1,4)
    denominator=plus(plus(const(1+xx*xx),times(const(2*xx),cosine)),const(0))
    numerator=plus(plus(const(1-xx*xx),times(const(2*xx),cosine)),times(const(2*xx*xx),square(cosine)))
    aval=neg(divide(times(const(xx),numerator),square(denominator)))
    log_real=times(const(F(1,2)),log_interval(denominator))
    angle=atan_interval(divide(times(const(xx),sine),plus(const(1),times(const(xx),cosine))))
    bval=neg(plus(times(cosine,log_real),times(sine,angle)))
    uu=const(F(4,9)); vv=log_interval(const(F(4,3)))
    first=times(plus(uu,aval),plus(vv,bval))
    second=times(plus(uu,neg(aval)),plus(vv,neg(bval)))
    # Both exact products are products of squared norms. Wide interval
    # dependency may give a negative lower endpoint; intersect with [0,infinity).
    assert first[1]>=0 and second[1]>=0
    first=(max(F(0),first[0]),first[1])
    second=(max(F(0),second[0]),second[1])
    return sqrt_interval(first)[1]+sqrt_interval(second)[1]


def mixed_cover(low,high,depth=0):
    bound=mixed_upper((low,high))
    if bound<F(173,250):
        return [{'c':[str(low),str(high)],'upper':str(bound)}]
    assert depth<16,'mixed cover failed'
    middle=(low+high)/2
    return mixed_cover(low,middle,depth+1)+mixed_cover(middle,high,depth+1)


def run_certificate(output):
    sine_upper=F(11,28)-F(11,28)**3/6+F(11,28)**5/120
    assert sine_upper<F(383,1000)
    radius=F(211,200)
    root_upper=F(57,100)
    assert radius*(root_upper-root_upper**3/6+root_upper**5/120)<root_upper
    assert 1-root_upper**2/2+root_upper**4/24-root_upper**6/720>F(21,25)
    assert upper_exp(radius*F(21,25))<F(672,277)
    assert upper_exp(radius)<F(800,277)
    ball=ball_cover(F(0),F(383,1000))
    mixed=mixed_cover(F(0),F(383,1000))
    record={'version':'0.20','c_max':'383/1000','T':'211/200','ball_cover':ball,'mixed_cover':mixed}
    if output:
        Path(output).write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':'PASS','ball_cells':len(ball),'ball_max_t_depth':max(max(row['t_depths']) for row in ball),
                      'mixed_cells':len(mixed),'mixed_max_bound':str(max(F(row['upper']) for row in mixed)),
                      'output':output},indent=2))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--test',action='store_true',required=True)
    parser.add_argument('--output')
    args=parser.parse_args()
    run_certificate(args.output)


if __name__=='__main__':
    main()
