#!/usr/bin/env python3
"""Arb/acb values with five validated real-coordinate derivatives.
Version 0.40 — Program B, 20261101__21:44 ET. Second-order forward rules with
whole-box centered value/gradient enclosures at each elementary operation.
"""
from flint import arb, acb


def real_square_ball(value):
    lower, upper = value.abs_lower(), value.abs_upper()
    lower, upper = (lower*lower).lower(), (upper*upper).upper()
    midpoint, radius = (lower+upper)/2, (upper-lower)/2
    return arb(midpoint.mid(), (radius+midpoint.rad()).upper())


class Differential:
    dimension = 5

    def __init__(self, value=0, gradient=None):
        self.value = acb(value)
        self.gradient = tuple(acb(0) for _ in range(self.dimension)) if gradient is None else tuple(gradient)
        if len(self.gradient) != self.dimension:
            raise ValueError('wrong derivative dimension')

    @classmethod
    def lift(cls, value):
        return value if isinstance(value, cls) else cls(value)

    @classmethod
    def variable(cls, value, index):
        gradient = [acb(0) for _ in range(cls.dimension)]
        gradient[index] = acb(1)
        return cls(value, gradient)

    def __add__(self, other):
        other = self.lift(other)
        return self.__class__(self.value+other.value,
                              [left+right for left, right in zip(self.gradient, other.gradient)])

    __radd__ = __add__

    def __neg__(self):
        return self.__class__(-self.value, [-item for item in self.gradient])

    def __sub__(self, other):
        return self+self.lift(other).__neg__()

    def __rsub__(self, other):
        return self.lift(other)-self

    def __mul__(self, other):
        other = self.lift(other)
        return self.__class__(self.value*other.value,
                              [left*other.value+self.value*right
                               for left, right in zip(self.gradient, other.gradient)])

    __rmul__ = __mul__

    def reciprocal(self):
        value = 1/self.value
        return self.__class__(value, [-item*value*value for item in self.gradient])

    def __truediv__(self, other):
        return self*self.lift(other).reciprocal()

    def __rtruediv__(self, other):
        return self.lift(other)/self

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError('only nonnegative integer polynomial powers supported')
        result = self.__class__(1)
        for _ in range(exponent):
            result = result*self
        return result

    def __gt__(self, other):
        if not self.value.imag.is_zero():
            raise TypeError('only real differential quantities can be ordered')
        return self.value.real > self.lift(other).value.real

    def unary(self, value, derivative):
        return self.__class__(value, [derivative*item for item in self.gradient])

    def exp(self):
        value = self.value.exp()
        return self.unary(value, value)

    def log(self):
        return self.unary(self.value.log(), 1/self.value)

    def sqrt(self):
        value = self.value.sqrt()
        return self.unary(value, 1/(2*value))

    def atanh(self):
        return self.unary(self.value.atanh(), 1/(1-self.value*self.value))

    def conjugate(self):
        return self.__class__(self.value.conjugate(), [item.conjugate() for item in self.gradient])

    @property
    def real(self):
        return self.__class__(self.value.real, [acb(item.real) for item in self.gradient])

    @property
    def imag(self):
        return self.__class__(self.value.imag, [acb(item.imag) for item in self.gradient])

    def square_real(self):
        if not self.value.imag.is_zero():
            raise TypeError('real square requires a real quantity')
        return self.__class__(real_square_ball(self.value.real),
                              [2*self.value*item for item in self.gradient])

    def is_finite(self):
        return self.value.is_finite() and all(item.is_finite() for item in self.gradient)

    def with_value(self, value):
        """Keep derivatives; caller must prove the replacement encloses the SAME function."""
        return self.__class__(value, self.gradient)


def complex_ball(real=0, imag=0):
    if isinstance(real, Differential) or isinstance(imag, Differential):
        prototype = real if isinstance(real, Differential) else imag
        if isinstance(imag, SecondDifferential):
            prototype = imag
        kind = type(prototype)
        return kind.lift(real)+acb(0, 1)*kind.lift(imag)
    return acb(real, imag)


class SecondDifferential(Differential):
    box_offsets = None

    @classmethod
    def set_box(cls, offsets):
        if len(offsets) != cls.dimension or not all(value.contains(0) for value in offsets):
            raise ValueError('the real box must contain its chosen center')
        cls.box_offsets = tuple(offsets)

    @staticmethod
    def intersect(first, second):
        if not first.is_finite() or not second.is_finite():
            return first
        return acb(first.real.intersection(second.real), first.imag.intersection(second.imag))

    def __init__(self, value=0, gradient=None, hessian=None, center_value=None, center_gradient=None):
        super().__init__(value, gradient)
        self.hessian = (tuple(tuple(acb(0) for _ in range(self.dimension)) for _ in range(self.dimension))
                        if hessian is None else tuple(tuple(row) for row in hessian))
        self.center_value = self.value if center_value is None else acb(center_value)
        self.center_gradient = self.gradient if center_gradient is None else tuple(center_gradient)
        if self.box_offsets is not None:
            self.gradient = tuple(self.intersect(self.gradient[row], self.center_gradient[row]+sum(
                self.hessian[row][column]*self.box_offsets[column] for column in range(self.dimension)))
                for row in range(self.dimension))
            self.value = self.intersect(self.value, self.center_value+sum(
                derivative*offset for derivative, offset in zip(self.gradient, self.box_offsets)))

    @classmethod
    def variable(cls, value, index):
        gradient = [acb(0) for _ in range(cls.dimension)]
        gradient[index] = acb(1)
        value = acb(value)
        if not value.imag.is_zero():
            raise TypeError('independent coordinates must be real')
        return cls(value, gradient, center_value=acb(value.real.mid()), center_gradient=gradient)

    def __add__(self, other):
        other = self.lift(other)
        return self.__class__(self.value+other.value,
                              [left+right for left, right in zip(self.gradient, other.gradient)],
                              [[self.hessian[row][column]+other.hessian[row][column]
                                for column in range(self.dimension)] for row in range(self.dimension)],
                              self.center_value+other.center_value,
                              [left+right for left, right in zip(self.center_gradient, other.center_gradient)])

    __radd__ = __add__

    def __neg__(self):
        return self.__class__(-self.value, [-item for item in self.gradient],
                              [[-item for item in row] for row in self.hessian],
                              -self.center_value, [-item for item in self.center_gradient])

    def __mul__(self, other):
        other = self.lift(other)
        hessian = [[self.hessian[row][column]*other.value+self.value*other.hessian[row][column]
                    +self.gradient[row]*other.gradient[column]+self.gradient[column]*other.gradient[row]
                    for column in range(self.dimension)] for row in range(self.dimension)]
        return self.__class__(self.value*other.value,
                              [left*other.value+self.value*right
                               for left, right in zip(self.gradient, other.gradient)], hessian,
                              self.center_value*other.center_value,
                              [left*other.center_value+self.center_value*right
                               for left, right in zip(self.center_gradient, other.center_gradient)])

    __rmul__ = __mul__

    def unary_second(self, value, first, second, center_value, center_first):
        hessian = [[first*self.hessian[row][column]+second*self.gradient[row]*self.gradient[column]
                    for column in range(self.dimension)] for row in range(self.dimension)]
        return self.__class__(value, [first*item for item in self.gradient], hessian,
                              center_value, [center_first*item for item in self.center_gradient])

    def reciprocal(self):
        value = 1/self.value
        center = 1/self.center_value
        return self.unary_second(value, -value*value, 2*value*value*value, center, -center*center)

    def exp(self):
        value = self.value.exp()
        center = self.center_value.exp()
        return self.unary_second(value, value, value, center, center)

    def log(self):
        inverse = 1/self.value
        return self.unary_second(self.value.log(), inverse, -inverse*inverse,
                                 self.center_value.log(), 1/self.center_value)

    def sqrt(self):
        value = self.value.sqrt()
        center = self.center_value.sqrt()
        return self.unary_second(value, 1/(2*value), -1/(4*value*value*value), center, 1/(2*center))

    def atanh(self):
        inverse = 1/(1-self.value*self.value)
        return self.unary_second(self.value.atanh(), inverse, 2*self.value*inverse*inverse,
                                 self.center_value.atanh(), 1/(1-self.center_value*self.center_value))

    def conjugate(self):
        return self.__class__(self.value.conjugate(), [item.conjugate() for item in self.gradient],
                              [[item.conjugate() for item in row] for row in self.hessian],
                              self.center_value.conjugate(), [item.conjugate() for item in self.center_gradient])

    @property
    def real(self):
        return self.__class__(self.value.real, [acb(item.real) for item in self.gradient],
                              [[acb(item.real) for item in row] for row in self.hessian],
                              self.center_value.real, [acb(item.real) for item in self.center_gradient])

    @property
    def imag(self):
        return self.__class__(self.value.imag, [acb(item.imag) for item in self.gradient],
                              [[acb(item.imag) for item in row] for row in self.hessian],
                              self.center_value.imag, [acb(item.imag) for item in self.center_gradient])

    def square_real(self):
        if not self.value.imag.is_zero():
            raise TypeError('real square requires a real quantity')
        return self.unary_second(real_square_ball(self.value.real), 2*self.value, acb(2),
                                 real_square_ball(self.center_value.real), 2*self.center_value)

    def is_finite(self):
        return super().is_finite() and all(item.is_finite() for row in self.hessian for item in row)

    def with_value(self, value):
        return self.__class__(value, self.gradient, self.hessian, self.center_value, self.center_gradient)
