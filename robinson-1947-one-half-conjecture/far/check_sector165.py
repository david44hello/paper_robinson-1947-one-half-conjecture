#!/usr/bin/env python3
"""Robinson 1947 exact sector certificate, program a, 20261101__19:49 ET.
Version 0.10: Fraction polynomial construction and dyadic Bernstein positivity.
"""
from fractions import Fraction as F
from math import comb, factorial
import json


def add(a, b):
    c = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return c


def scale(a, x):
    return [x*v for v in a]


def mul(a, b):
    c = [F(0)] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def power(a, n):
    c = [F(1)]
    for _ in range(n):
        c = mul(c, a)
    return c


def lower_exp(x, n=12):
    return sum((x**j/F(factorial(j)) for j in range(n+1)), F(0))


def upper_exp(x, n=12):
    assert 0 <= x < n+2
    return lower_exp(x,n)+x**(n+1)/F(factorial(n+1))/(1-x/F(n+2))


def split(b):
    row = b[:]
    left, right = [row[0]], [row[-1]]
    while len(row)>1:
        row = [(x+y)/2 for x,y in zip(row,row[1:])]
        left.append(row[0])
        right.append(row[-1])
    return left, right[::-1]


def main():
    den = [F(1), F(0), F(1)]
    cn = [F(253,2000), F(59,50), -F(253,2000)]
    dn = [F(11,10), F(1357,10000), -F(11,10)]
    un = add(scale(den,F(26,25)),scale(cn,-1))
    en = [F(0)]
    for j in range(9):
        en = add(en,scale(mul(power(un,j),power(den,8-j)),F(1,factorial(j))))
    co = power(den,6)
    for j, coeff in [(2,-F(1,2)),(4,F(1,24)),(6,-F(1,720))]:
        co = add(co,scale(mul(power(dn,j),power(den,6-j)),coeff))
    poly = add(mul(en,co),scale(power(den,14),-1))
    assert len(poly)==29
    bern = [sum((poly[i]*F(comb(k,i),comb(28,i)) for i in range(k+1)),F(0)) for k in range(29)]
    cover=[]
    def visit(b,lo,hi,depth):
        if min(b)>0:
            cover.append({'lo':str(lo),'hi':str(hi),'min_bernstein':str(min(b))})
            return
        assert depth<16, 'Certificate failed to close within depth 16'
        l,r=split(b)
        mid=(lo+hi)/2
        visit(l,lo,mid,depth+1)
        visit(r,mid,hi,depth+1)
    visit(bern,F(0),F(1),0)
    checks={
        'atanh_upper':lower_exp(F(2747,2500))>3,
        'atan_lower':sum(((-1)**j*F(1,2)**(2*j+1)/F(2*j+1) for j in range(6)),F(0))>F(1159,2500),
        'd_upper':4*(F(2747,5000)**2-F(1159,2500)**2)<F(59,100)**2,
        'R_upper':lower_exp(F(11,10))>3,
        'log_ratio':lower_exp(F(53,250))>F(58,47),
        'cos_phi':F(53,1000)/F(1159,2500)<F(23,200),
        'u_positive':F(253,2000)+F(59,100)<F(26,25),
        'D_bound':F(11,10)**2+F(1357,20000)**2<F(6,5)**2,
        'cos_lower_positive':1-F(6,5)**2/2-F(6,5)**6/720>0,
        'alpha_half':F(26,25)*(F(1,2)-F(1,2)**3/6+F(1,2)**5/120)<F(1,2),
        'cos_half':1-F(1,2)**2/2>=F(7,8),
        'exp_endpoint_7over8':upper_exp(F(91,100))<F(875,351),
        'exp_endpoint_1':upper_exp(F(26,25))<F(1000,351),
        'log_4over3_upper':lower_exp(F(287683,1000000))>F(4,3),
        'log_5over4_lower':upper_exp(F(223143,1000000))<F(5,4),
        'log_5over4_upper':lower_exp(F(223144,1000000))>F(5,4),
    }
    eps=F(11,42)
    du=F(3,32)*eps**2
    dv=F(33,1000)*eps**2
    p1=(F(4,9)-F(4,25)+du)*(F(287683,1000000)-F(223143,1000000)+dv)
    p2=(F(4,9)+F(4,25)+du)*(F(287683,1000000)+F(223144,1000000)+dv)
    checks['mixed_first']=p1<F(7,50)**2
    checks['mixed_second']=p2<F(14,25)**2
    print(json.dumps({'checks':checks,'degree':28,'cover':cover},indent=2))
    assert all(checks.values()), 'One or more scalar inequalities failed'


if __name__=='__main__':
    main()
