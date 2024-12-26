from hashlib import sha256
from app.ecdsa import *
import secrets


class FieldElement:
	def __init__(self, num, prime):
		if num >= prime or num < 0:
			error = 'Num {} not in field range 0 to {}'.format(num, prime - 1)
			raise ValueError(error)
		self.num = num
		self.prime = prime

	def __repr__(self):
		return 'FieldElement_{}({})'.format(self.prime, self.num)

	def __eq__(self, other):
		if other is None:
			return False
		return self.num == other.num and self.prime == other.prime
	
	def __add__(self, other):
		if self.prime != other.prime:
			raise TypeError('Cannot add two numbers in different Fields')
		num = (self.num + other.num) % self.prime
		return self.__class__(num, self.prime)
	
	def __sub__(self, other):
		if self.prime != other.prime:
			raise TypeError('Cannot sub two numbers in different Fields')
		num = (self.num - other.num) % self.prime
		return self.__class__(num, self.prime)
	
	def __mul__(self,other):
		if self.prime != other.prime:
			raise TypeError('Cannot mul two numbers in different Fields')
		num = (self.num * other.num) % self.prime
		return self.__class__(num, self.prime)
	
	def __pow__(self,exponent):
		n = exponent
		while n<0:
			n += self.prime-1
		num = (self.num ** n) % self.prime
		return self.__class__(num, self.prime)
	
	def __ne__(self, other: object) -> bool:
		if other is None:
			return False
		return self.num != other.num or self.prime != other.prime
	
	def __truediv__(self, other):
		if self.prime != other.prime:
			raise TypeError('Cannot divide two numbers in different Fields')
		# self.num and other.num are the actual values
		# self.prime is what we need to mod against
		# use fermat's little theorem:
		# self.num**(p-1) % p == 1
		# this means:
		# 1/n == pow(n, p-2, p)
		num = (self.num * pow(other.num, self.prime - 2, self.prime)) % self.prime
		# We return an element of the same class
		return self.__class__(num, self.prime)

	def __rmul__(self, coefficient):
		num = (self.num * coefficient) % self.prime
		return self.__class__(num=num, prime=self.prime)


class Point:
	def __init__(self, x, y, a, b):
		self.a = a
		self.b = b
		self.x = x
		self.y = y
		if self.x is None and self.y is None:
			return
		if self.y**2 != self.x**3 + a * x + b:
			raise ValueError('({}, {}) is not on the curve'.format(x, y))

	def __repr__(self):
		if self.x is None:
			return 'Point(infinity)'
		elif isinstance(self.x, FieldElement):
			return 'Point({},{})_{}_{} FieldElement({})'.format(
				self.x.num, self.y.num, self.a.num, self.b.num, self.x.prime)
		else:
			return 'Point({},{})_{}_{}'.format(self.x, self.y, self.a, self.b)

	def __eq__(self, other):
		return self.x == other.x and self.y == other.y \
			and self.a == other.a and self.b == other.b
	
	def __add__(self, other):
		if self.a != other.a or self.b != other.b:
			raise TypeError('Points {}, {} are not on the same curve'.format(self, other))
		if self.x is None:
			return other
		if other.x is None:
			return self
		if self.x == other.x and self.y != other.y:
			return self.__class__(None, None, self.a, self.b)
		if self.x != other.x:
			s = (other.y - self.y) / (other.x - self.x)
			x = s**2 - self.x - other.x
			y = s * (self.x - x) - self.y
			return self.__class__(x, y, self.a, self.b)
		if self == other and self.y == 0 * self.x:
			return self.__class__(None, None, self.a, self.b)
		if self == other:
			s = (3 * self.x**2 + self.a) / (2 * self.y)
			x = s**2 - 2 * self.x
			y = s * (self.x - x) - self.y
			return self.__class__(x, y, self.a, self.b)
	
	def __ne__(self, other):
		return not (self == other)
	
	def __rmul__(self, coefficient):
		coef = coefficient
		current = self  # <1>
		result = self.__class__(None, None, self.a, self.b)  # <2>
		while coef:
			if coef & 1:  # <3>
				result += current
			current += current  # <4>
			coef >>= 1  # <5>
		return result




class S256Field(FieldElement):
   
    def __init__(self, num, prime= 2**256 - 2**32 - 977):
        super().__init__(num=num,prime = 2**256 - 2**32 - 977)

    def __repr__(self):
        return '{:x}'.format(self.num).zfill(64)
    
class S256Point(Point):
    A = 0
    B = 7
    N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
    
    def __init__(self, x, y, a=None, b=None):
        a, b = S256Field(self.A), S256Field(self.B)
        if type(x) == int:
            super().__init__(x=S256Field(x), y=S256Field(y), a=a, b=b)
        else:
            super().__init__(x=x, y=y, a=a, b=b)

    def __rmul__(self, coefficient):
        coef = coefficient % self.N
        return super().__rmul__(coef)
    
    def __repr__(self):
        if self.x is None:
            return 'S256Point(infinity)'
        else:
            return 'S256Point({}, {})'.format(self.x, self.y)
   
   
    def verify(self, z, sig):
        G = S256Point(0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)
        s_inv = pow(sig.s, self.N - 2, self.N)
        u = z * s_inv % self.N
        v = sig.r * s_inv % self.N
        total = u * G + v * self
        return total.x.num == sig.r   
    

class Signature:
    def __init__(self, z,e):
        G = S256Point(0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)
        k = secrets.randbelow(S256Point.N-1)+1
        k_inv = pow(k, S256Point.N - 2, S256Point.N)
        self.r = (k * G).x.num
        self.s = (z + self.r * e) * k_inv % S256Point.N
    
    def __repr__(self):
        return 'Signature({:x},{:x})'.format(self.r, self.s)


class PublicKey:
    G = S256Point(0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)

    def __init__(self, secret):
        self.secret = secret
        self.point = secret * self.G
        
    def hex(self):
        return '{:x}'.format(self.secret).zfill(64)



def hash256(s):
    '''two rounds of sha256'''
    return sha256(sha256(s).digest()).digest()    