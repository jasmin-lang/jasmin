from __future__ import print_function
import sys
import logging
import random

sys.ps1 = ""

# * Reference implementation
###########################################################################

# see https://raw.githubusercontent.com/warner/python-pure25519/master/pure25519/basic.py

# "python-pure25519" Copyright (c) 2015 Brian Warner and other contributors

# Permission is hereby granted, free of charge, to any person
# obtaining a copy of this software and associated documentation
# files (the "Software"), to deal in the Software without
# restriction, including without limitation the rights to use,
# copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the
# Software is furnished to do so, subject to the following
# conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
# OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
# HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
# WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
# OTHER DEALINGS IN THE SOFTWARE.

import binascii, hashlib, itertools

Q = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493

def inv(x):
  return pow(x, Q-2, Q)

d = -121665 * inv(121666)
I = pow(2,(Q-1)//4,Q)

def xrecover(y):
  xx = (y*y-1) * inv(d*y*y+1)
  x = pow(xx,(Q+3)//8,Q)
  if (x*x - xx) % Q != 0: x = (x*I) % Q
  if x % 2 != 0: x = Q-x
  return x

By = 4 * inv(5)
Bx = xrecover(By)
B = [Bx % Q,By % Q]

# Extended Coordinates: x=X/Z, y=Y/Z, x*y=T/Z
# http://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html

def xform_affine_to_extended(pt):
  (x, y) = pt
  return (x%Q, y%Q, 1, (x*y)%Q) # (X,Y,Z,T)

def xform_extended_to_affine(pt):
  (x, y, z, _) = pt
  return ((x*inv(z))%Q, (y*inv(z))%Q)

def double_element(pt): # extended->extended
  # dbl-2008-hwcd
  (X1, Y1, Z1, _) = pt
  A = (X1*X1)
  B = (Y1*Y1)
  C = (2*Z1*Z1)
  D = (-A) % Q
  J = (X1+Y1) % Q
  E = (J*J-A-B) % Q
  G = (D+B) % Q
  F = (G-C) % Q
  H = (D-B) % Q
  X3 = (E*F) % Q
  Y3 = (G*H) % Q
  Z3 = (F*G) % Q
  T3 = (E*H) % Q
  return (X3, Y3, Z3, T3)

def add_elements(pt1, pt2): # extended->extended
  # add-2008-hwcd-3 . Slightly slower than add-2008-hwcd-4, but -3 is
  # unified, so it's safe for general-purpose addition
  (X1, Y1, Z1, T1) = pt1
  (X2, Y2, Z2, T2) = pt2
  A = ((Y1-X1)*(Y2-X2)) % Q
  B = ((Y1+X1)*(Y2+X2)) % Q
  C = T1*(2*d)*T2 % Q
  D = Z1*2*Z2 % Q
  E = (B-A) % Q
  F = (D-C) % Q
  G = (D+C) % Q
  H = (B+A) % Q
  X3 = (E*F) % Q
  Y3 = (G*H) % Q
  T3 = (E*H) % Q
  Z3 = (F*G) % Q
  return (X3, Y3, Z3, T3)

def scalarmult_element_safe_slow(pt, n):
  # this form is slightly slower, but tolerates arbitrary points, including
  # those which are not in the main 1*L subgroup. This includes points of
  # order 1 (the neutral element Zero), 2, 4, and 8.
  assert n >= 0
  if n==0:
    return xform_affine_to_extended((0,1))
  _ = double_element(scalarmult_element_safe_slow(pt, n>>1))
  return add_elements(_, pt) if n&1 else _

def _add_elements_nonunfied(pt1, pt2): # extended->extended
  # add-2008-hwcd-4 : NOT unified, only for pt1!=pt2. About 10% faster than
  # the (unified) add-2008-hwcd-3, and safe to use inside scalarmult if you
  # aren't using points of order 1/2/4/8
  (X1, Y1, Z1, T1) = pt1
  (X2, Y2, Z2, T2) = pt2
  A = ((Y1-X1)*(Y2+X2)) % Q
  B = ((Y1+X1)*(Y2-X2)) % Q
  C = (Z1*2*T2) % Q
  D = (T1*2*Z2) % Q
  E = (D+C) % Q
  F = (B-A) % Q
  G = (B+A) % Q
  H = (D-C) % Q
  X3 = (E*F) % Q
  Y3 = (G*H) % Q
  Z3 = (F*G) % Q
  T3 = (E*H) % Q
  return (X3, Y3, Z3, T3)

def scalarmult_element(pt, n): # extended->extended
  # This form only works properly when given points that are a member of
  # the main 1*L subgroup. It will give incorrect answers when called with
  # the points of order 1/2/4/8, including point Zero. (it will also work
  # properly when given points of order 2*L/4*L/8*L)
  assert n >= 0
  if n==0:
      return xform_affine_to_extended((0,1))
  _ = double_element(scalarmult_element(pt, n>>1))
  return _add_elements_nonunfied(_, pt) if n&1 else _

# points are encoded as 32-bytes little-endian, b255 is sign, b2b1b0 are 0

def encodepoint(P):
  x = P[0]
  y = P[1]
  # MSB of output equals x.b0 (=x&1)
  # rest of output is little-endian y
  assert 0 <= y < (1<<255) # always < 0x7fff..ff
  if x & 1:
    y += 1<<255
  return binascii.unhexlify("%064x" % y)[::-1]

def isoncurve(P):
  x = P[0]
  y = P[1]
  return (-x*x + y*y - 1 - d*x*x*y*y) % Q == 0

class NotOnCurve(Exception):
  pass

def decodepoint(s):
  unclamped = int(binascii.hexlify(s[:32][::-1]), 16)
  clamp = (1 << 255) - 1
  y = unclamped & clamp # clear MSB
  x = xrecover(y)
  if bool(x & 1) != bool(unclamped & (1<<255)): x = Q-x
  P = [x,y]
  if not isoncurve(P): raise NotOnCurve("decoding point that is not on curve")
  return P

# scalars are encoded as 32-bytes little-endian

def bytes_to_scalar(s):
  assert len(s) == 32, len(s)
  return int(binascii.hexlify(s[::-1]), 16)

def bytes_to_clamped_scalar(s):
  # Ed25519 private keys clamp the scalar to ensure two things:
  #   1: integer value is in L/2 .. L, to avoid small-logarithm
  #      non-wraparaound
  #   2: low-order 3 bits are zero, so a small-subgroup attack won't learn
  #      any information
  # set the top two bits to 01, and the bottom three to 000
  a_unclamped = bytes_to_scalar(s)
  AND_CLAMP = (1<<254) - 1 - 7
  OR_CLAMP = (1<<254)
  a_clamped = (a_unclamped & AND_CLAMP) | OR_CLAMP
  return a_clamped

def random_scalar(entropy_f): # 0..L-1 inclusive
  # reduce the bias to a safe level by generating 256 extra bits
  oversized = int(binascii.hexlify(entropy_f(32+32)), 16)
  return oversized % L

def password_to_scalar(pw):
  oversized = hashlib.sha512(pw).digest()
  return int(binascii.hexlify(oversized), 16) % L

def scalar_to_bytes(y):
  y = y % L
  assert 0 <= y < 2**256
  return binascii.unhexlify("%064x" % y)[::-1]

# Elements, of various orders

def is_extended_zero(XYTZ):
  # catch Zero
  (X, Y, Z, T) = XYTZ
  Y = Y % Q
  Z = Z % Q
  if X==0 and Y==Z and Y!=0:
    return True
  return False

class ElementOfUnknownGroup:
  # This is used for points of order 2,4,8,2*L,4*L,8*L
  def __init__(self, XYTZ):
    assert isinstance(XYTZ, tuple)
    assert len(XYTZ) == 4
    self.XYTZ = XYTZ

  def add(self, other):
    if not isinstance(other, ElementOfUnknownGroup):
      raise TypeError("elements can only be added to other elements")
    sum_XYTZ = add_elements(self.XYTZ, other.XYTZ)
    if is_extended_zero(sum_XYTZ):
      return Zero
    return ElementOfUnknownGroup(sum_XYTZ)

  def scalarmult(self, s):
    if isinstance(s, ElementOfUnknownGroup):
      raise TypeError("elements cannot be multiplied together")
    assert s >= 0
    product = scalarmult_element_safe_slow(self.XYTZ, s)
    return ElementOfUnknownGroup(product)

  def to_bytes(self):
    return encodepoint(xform_extended_to_affine(self.XYTZ))
  def __eq__(self, other):
    return self.to_bytes() == other.to_bytes()
  def __ne__(self, other):
    return not self == other

class Element(ElementOfUnknownGroup):
  # this only holds elements in the main 1*L subgroup. It never holds Zero,
  # or elements of order 1/2/4/8, or 2*L/4*L/8*L.

  def add(self, other):
    if not isinstance(other, ElementOfUnknownGroup):
      raise TypeError("elements can only be added to other elements")
    sum_element = ElementOfUnknownGroup.add(self, other)
    if sum_element is Zero:
      return sum_element
    if isinstance(other, Element):
      # adding two subgroup elements results in another subgroup
      # element, or Zero, and we've already excluded Zero
      return Element(sum_element.XYTZ)
    # not necessarily a subgroup member, so assume not
    return sum_element

  def scalarmult(self, s):
    if isinstance(s, ElementOfUnknownGroup):
      raise TypeError("elements cannot be multiplied together")
    # scalarmult of subgroup members can be done modulo the subgroup
    # order, and using the faster non-unified function.
    s = s % L
    # scalarmult(s=0) gets you Zero
    if s == 0:
      return Zero
    # scalarmult(s=1) gets you self, which is a subgroup member
    # scalarmult(s<grouporder) gets you a different subgroup member
    return Element(scalarmult_element(self.XYTZ, s))

  # negation and subtraction only make sense for the main subgroup
  def negate(self):
    # slow. Prefer e.scalarmult(-pw) to e.scalarmult(pw).negate()
    return Element(scalarmult_element(self.XYTZ, L-2))
  def subtract(self, other):
    return self.add(other.negate())

class _ZeroElement(ElementOfUnknownGroup):
  def add(self, other):
    return other # zero+anything = anything
  def scalarmult(self, s):
    return self # zero*anything = zero
  def negate(self):
    return self # -zero = zero
  def subtract(self, other):
    return self.add(other.negate())

Base = Element(xform_affine_to_extended(B))
Zero = _ZeroElement(xform_affine_to_extended((0,1))) # the neutral (identity) element

_zero_bytes = Zero.to_bytes()


def arbitrary_element(seed): # unknown DL
  # TODO: if we don't need uniformity, maybe use just sha256 here?
  hseed = hashlib.sha512(seed).digest()
  y = int(binascii.hexlify(hseed), 16) % Q

  # we try successive Y values until we find a valid point
  for plus in itertools.count(0):
    y_plus = (y + plus) % Q
    x = xrecover(y_plus)
    Pa = [x,y_plus] # no attempt to use both "positive" and "negative" X

    # only about 50% of Y coordinates map to valid curve points (I think
    # the other half give you points on the "twist").
    if not isoncurve(Pa):
      continue

    P = ElementOfUnknownGroup(xform_affine_to_extended(Pa))
    # even if the point is on our curve, it may not be in our particular
    # (order=L) subgroup. The curve has order 8*L, so an arbitrary point
    # could have order 1,2,4,8,1*L,2*L,4*L,8*L (everything which divides
    # the group order).

    # [I MAY BE COMPLETELY WRONG ABOUT THIS, but my brief statistical
    # tests suggest it's not too far off] There are phi(x) points with
    # order x, so:
    #  1 element of order 1: [(x=0,y=1)=Zero]
    #  1 element of order 2 [(x=0,y=-1)]
    #  2 elements of order 4
    #  4 elements of order 8
    #  L-1 elements of order L (including Base)
    #  L-1 elements of order 2*L
    #  2*(L-1) elements of order 4*L
    #  4*(L-1) elements of order 8*L

    # So 50% of random points will have order 8*L, 25% will have order
    # 4*L, 13% order 2*L, and 13% will have our desired order 1*L (and a
    # vanishingly small fraction will have 1/2/4/8). If we multiply any
    # of the 8*L points by 2, we're sure to get an 4*L point (and
    # multiplying a 4*L point by 2 gives us a 2*L point, and so on).
    # Multiplying a 1*L point by 2 gives us a different 1*L point. So
    # multiplying by 8 gets us from almost any point into a uniform point
    # on the correct 1*L subgroup.

    P8 = P.scalarmult(8)

    # if we got really unlucky and picked one of the 8 low-order points,
    # multiplying by 8 will get us to the identity (Zero), which we check
    # for explicitly.
    if is_extended_zero(P8.XYTZ):
      continue

    # Test that we're finally in the right group. We want to scalarmult
    # by L, and we want to *not* use the trick in Group.scalarmult()
    # which does x%L, because that would bypass the check we care about.
    # P is still an _ElementOfUnknownGroup, which doesn't use x%L because
    # that's not correct for points outside the main group.
    assert is_extended_zero(P8.scalarmult(L).XYTZ)

    return Element(P8.XYTZ)
  # never reached

def bytes_to_unknown_group_element(bytes):
  # this accepts all elements, including Zero and wrong-subgroup ones
  if bytes == _zero_bytes:
    return Zero
  XYTZ = xform_affine_to_extended(decodepoint(bytes))
  return ElementOfUnknownGroup(XYTZ)

def bytes_to_element(bytes):
  # this strictly only accepts elements in the right subgroup
  P = bytes_to_unknown_group_element(bytes)
  if P is Zero:
    raise ValueError("element was Zero")
  if not is_extended_zero(P.scalarmult(L).XYTZ):
    raise ValueError("element is not in the right group")
  # the point is in the expected 1*L subgroup, not in the 2/4/8 groups,
  # or in the 2*L/4*L/8*L groups. Promote it to a correct-group Element.
  return Element(P.XYTZ)

# * Functions callable from dmasm
###########################################################################

def confirm_started():
  print("done", file=sys.stdout)

def print_newline(params):
  print("", file=sys.stderr)
  return []

def assert_equal(x, y, params):
  assert (x == y)
  return []

def to_digits(radix,digits,n):
  res = [0] * digits
  for i in range(digits):
    res[i] = n % radix
    n = n / radix
  assert (n == 0)
  return res

def from_digits(radix,digits):
  res = 0
  for i,n in enumerate(digits):
    res = res + n*(radix**i)
  return res

def print_u64_arr(x,params):
  print('>>> print_u64_arr: x=%s'%(str(x)), file=sys.stderr)
  y = from_digits(2**64,x) # % p
  #print('>>> print_u64_arr: x=%s'%(str(y)), file=sys.stderr)
  #print('>>> print_u64_arr: n=%s'%(str(params['n'])), file=sys.stderr)
  return []

def print_u64(x,params):
  print('%s '%(str(x)), file=sys.stderr, end="")
  return []

def rand_point(seed,params):
  a = arbitrary_element("%i"%seed)
  ab = a.to_bytes()
  ai = int(ab.encode('hex'), 16)
  # print("point %s"%(str(ai)),file=sys.stderr)
  x = to_digits(two64,4,ai)
  return x

# * AVX vector instructions
###########################################################################

# ** General

def mod_n(n,x):
  return x & ((1 << n) - 1)

# ** 8 bit

def get_8x32(i,x):
  return mod_n(8,x >> i*8)

def mk_8x32(x):
  r = 0
  for i in range(0,32):
    r += x[i] << 8*i
  return r

def blend_8x32(v1,v2,v3,params):
  w = [0] * 32
  for i in range(0,32):
    b = get_8x32(i,v3)
    if b == 0:
      # print('>>> get first', file=sys.stderr)
      w[i] = get_8x32(i,v1)
    else:
      # print('>>> get second', file=sys.stderr)
      w[i] = get_8x32(i,v2)
  r = mk_8x32(w)
  # print('>>> v1=%064x'%(v1), file=sys.stderr)
  # print('>>> v2=%064x'%(v2), file=sys.stderr)
  # print('>>>  r=%064x'%(r),  file=sys.stderr)
  return r

# ** 64 bit

def get_64x4(i,x):
  return mod_n(64,x >> i*64)

def mk_64x4(x):
  r = 0
  for i in range(0,4):
    r += x[i] << 64*i
  return r 

def add_64x4(x,y,params):
  z = [0] * 4
  for i in range(0,4):
    z[i] = mod_n(64,get_64x4(i,x) + get_64x4(i,y))
  r = mk_64x4(z)
  # print('>>> r: x=%02x'%(r), file=sys.stderr)
  return r

def permute_64x4(v,c,params):
  # print('>>> c=%02x'%(c), file=sys.stderr)
  # print('>>> v=%064x'%(v), file=sys.stderr)
  w = [0] * 4
  for i in range(0,4):
    s = (c >> 2*i) % 4
    w[i] = get_64x4(s,v)
  r = mk_64x4(w)
  # print('>>> r=%064x'%(r), file=sys.stderr)
  return r

def shift_right_64x4(v,c,params):
  w = [0] * 4
  for i in range(0,4):
    w[i] = get_64x4(i,v) >> c
  r = mk_64x4(w)
  # print('>>> r=%064x'%(r), file=sys.stderr)
  return r

def shift_left_64x4(v,c,params):
  w = [0] * 4
  for i in range(0,4):
    w[i] = mod_n(64,get_64x4(i,v) << c)
    # print('>>> v[i]=%08x'%(get_64x4(i,v)), file=sys.stderr)
    # print('>>> w[i]=%08x'%(w[i]), file=sys.stderr)
  r = mk_64x4(w)
  # print('>>> v=%064x'%(v), file=sys.stderr)
  # print('>>> r=%064x'%(r), file=sys.stderr)
  return r

def set_64x4(x,params):
  return mk_64x4(x)

def extract_64x4(x,params):
  w = [0] * 4
  for i in range(0,4):
    w[i] = get_64x4(i,x)
  return w

# ** 32 bit

def get_32x8(i,x):
  return mod_n(32,x >> i*32)

def mk_32x8(x):
  r = 0
  for i in range(0,8):
    r += x[i] << 32*i
  return r 

def set_32x8(x7,x6,x5,x4,x3,x2,x1,x0,params):
  return mk_32x8([x0,x1,x2,x3,x4,x5,x6,x7])

def shuffle_32x8(v,c,params):
  # print('>>> c=%02x'%(c), file=sys.stderr)
  # print('>>> v=%064x'%(v), file=sys.stderr)
  w = [0] * 8
  for i in range(0,4):
    s = (c >> 2*i) % 4
    w[i] = get_32x8(s,v)
  for i in range(0,4):
    s = (c >> 2*i) % 4
    w[4+i] = get_32x8(4 + s,v)
  r = mk_32x8(w)
  # print('>>> r=%064x'%(r), file=sys.stderr)
  return r

def add_32x8(x,y,params):
  z = [0] * 8
  for i in range(0,8):
    z[i] = mod_n(32,get_32x8(i,x) + get_32x8(i,y))
  r = mk_32x8(z)
  # print('>>> r: x=%02x'%(r), file=sys.stderr)
  return r

def umul_32x4(x,y,params):
  z = [0] * 4
  for i in range(0,4):
    u = get_32x8(i*2,x) * get_32x8(i*2,y)
    z[i] = mod_n(64,u)
  r = mk_64x4(z)
  return r

def decode_i32(x):
  if x >> 31 == 0:
    return x
  else:
    return x - (1 << 32)

def encode_i32(x):
  if x < 0:
    return (1 << 32) + x
  else:
    return x

def imul_32x4(x,y,params):
  z = [0] * 4
  for i in range(0,4):
    u = decode_i32(get_32x8(i*2,x))
    v = decode_i32(get_32x8(i*2,y))
    z[i] = encode_i32(u*v)
  r = mk_64x4(z)
  # print('>>> r=%064x'%(r), file=sys.stderr)
  return r

def test_enc():
  assert(decode_i32(42) == 42)
  u = 0x80000000
  u = 1 << 31
  v = decode_i32(u)
  w = encode_i32(v)
  # print('>>> u=%02x'%(u), file=sys.stderr)
  # print('>>> v=%i'%(v), file=sys.stderr)
  # print('>>> w=%02x'%(w), file=sys.stderr)
  assert(u == w)

# test_enc()

# * Code from CFRG on curves (BSD licensed)
###########################################################################

# https://cdn.rawgit.com/agl/cfrgcurve/2429fd5b5b3be3362178bc59360d60ffc7f2a8b2/cfrgcurve.xml

bits_25517 = 255

def encodeLittleEndian(s):
  return ''.join([chr((s >> 8*i) & 0xff) for i in range((bits_25517+7)/8)])

def decodeLittleEndian(b):
  return sum([b[i] << 8*i for i in range((bits_25517+7)/8)])

def decodeUCoordinate(u):
  u_list = [ord(b) for b in u]
  # Ignore any unused bits.
  if bits_25517 % 8:
    u_list[-1] &= (1<<(bits_25517%8))-1
  return decodeLittleEndian(u_list)

def encodeUCoordinate(u):
  u = u % p
  return ''.join([chr((u >> 8*i) & 0xff) for i in range((bits_25517+7)/8)])

def decodeScalar25519(k):
  k_list = [ord(b) for b in k]
  k_list[0]  &= 248
  k_list[31] &= 127
  k_list[31] |= 64
  return decodeLittleEndian(k_list)

# * Functions for 25519 with 4 limbs
###########################################################################

p = 2**255 - 19
two64 = 2**64

def to_big_int(n):
  return (from_digits(two64,n) % p)

def rand(s,params):
  # print('>>> rand_arr: x=%s'%(str(s)), file=sys.stderr)
  random.seed(s)
  n = random.getrandbits(512) % (2**256) # p
  res = to_digits(two64,4,n)
  # print('>>> rand_arr: res=%s'%(str(res)), file=sys.stderr)
  return res

def rand_u64(s,params):
  # print('>>> rand_arr: x=%s'%(str(s)), file=sys.stderr)
  random.seed(s)
  res = random.getrandbits(64)
  return res

def assert_equal_add(x,y,z,params):
  xi = to_big_int(x)
  yi = to_big_int(y)
  zi = to_big_int(z)
  assert ((xi + yi) % p == (zi % p))
  return []

def assert_equal_sub(x,y,z,params):
  xi = to_big_int(x)
  yi = to_big_int(y)
  zi = to_big_int(z)
  assert ((xi - yi) % p == (zi % p))
  return []

def assert_equal_mul(x,y,z,params):
  xi = to_big_int(x)
  yi = to_big_int(y)
  zi = to_big_int(z)
  assert ((xi * yi) % p == (zi % p))
  return []

def assert_equal_u64(x,y,params):
  assert (x == y)
  return []

# translated from:
# https://github.com/agl/curve25519-donna/blob/master/curve25519-donna-c64.c
def fmonty( x, z            # Q
          , xprime, zprime  # Q'
          , qmqp            # Q - Q'
          ):
  origx = x                             # memcpy(origx, x, 5 * sizeof(limb))
  x = (x + z)                      % p  # fsum(x,z)
  z = (origx - z)                  % p  # fdifference_backwards(z, origx);
  origxprime = xprime                   # memcpy(origxprime, xprime, sizeof(limb) * 5)
  xprime = (xprime + zprime)       % p  # fsum(xprime, zprime)
  zprime = (origxprime - zprime)   % p  # fdifference_backwards(zprime, origxprime)
  xxprime = (xprime * z)           % p  # fmul(xxprime, xprime, z);
  zzprime = (x * zprime)           % p  # fmul(zzprime, x, zprime)
  origxprime = xxprime             % p  # memcpy(origxprime, xxprime, sizeof(limb) * 5)
  xxprime = (xxprime + zzprime)    % p  # fsum(xxprime, zzprime)
  zzprime = (origxprime - zzprime) % p  # fdifference_backwards(zzprime, origxprime)
  x3 = (xxprime * xxprime)         % p  # fsquare_times(x3, xxprime, 1)
  zzzprime = (zzprime * zzprime)   % p  # fsquare_times(zzzprime, zzprime, 1)
  z3 = (zzzprime * qmqp)           % p  # fmul(z3, zzzprime, qmqp)
  xx = (x * x)                     % p  # fsquare_times(xx, x, 1)
  zz = (z * z)                     % p  # fsquare_times(zz, z, 1)
  x2 = (xx * zz)                   % p  # fmul(x2, xx, zz)
  zz = (xx - zz)                   % p  # fdifference_backwards(zz, xx)
  zzz = (zz*121665)                % p  # fscalar_product(zzz, zz, 121665)
  zzz = (zzz + xx)                 % p  # fsum(zzz, xx)
  z2 = (zz * zzz)                  % p  # fmul(z2, zz, zzz)
  
  # return values:
  # x2, z2 = 2Q
  # x3, z3 = Q + Q' 
  return (x2,z2,x3,z3)


# translated from Verify25519 paper (Algorithm 2)
def ladderstep_tracing(x1, x2, z2, x3, z3):
  #print("monty input:\n%s\n"%(str((x1,x2,z2,x3,z3))), file=sys.stderr)
  t1 = (x2 + z2)     % p; l1  = t1
  t2 = (x2 - z2)     % p; l2  = t2
  t7 = (t2 * t2)     % p; l3  = t7
  t6 = (t1 * t1)     % p; l4  = t6
  t5 = (t6 - t7)     % p; l5  = t5
  t3 = (x3 + z3)     % p; l6  = t3
  t4 = (x3 - z3)     % p; l7  = t4
  t9 = (t3 * t2)     % p; l8  = t9
  t8 = (t4 * t1)     % p; l9  = t8
  x3 = (t8 + t9)     % p; l10 = x3

  z3 = (t8 - t9)     % p; l11 = z3
  x3 = (x3 * x3)     % p; l12 = x3
  z3 = (z3 * z3)     % p; l13 = z3
  z3 = (z3 * x1)     % p; l14 = z3
  x2 = (t6 * t7 )    % p; l15 = x2
  z2 = (121666 * t5) % p; l16 = z2
  z2 = (z2 + t7)     % p; l17 = z2
  z2 = (z2 * t5)     % p; l18 = z2

  #print("monty result:\n%s\n"%(str((x2,z2,x3,z3))), file=sys.stderr)
  return (l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16,l17,l18)

def ladderstep(x1, x2, z2, x3, z3):
  #print("monty input:\n%s\n"%(str((x1,x2,z2,x3,z3))), file=sys.stderr)
  t1 = (x2 + z2)     % p
  t2 = (x2 - z2)     % p
  t7 = (t2 * t2)     % p
  t6 = (t1 * t1)     % p
  t5 = (t6 - t7)     % p
  t3 = (x3 + z3)     % p
  t4 = (x3 - z3)     % p
  t9 = (t3 * t2)     % p
  t8 = (t4 * t1)     % p
  x3 = (t8 + t9)     % p

  z3 = (t8 - t9)     % p
  x3 = (x3 * x3)     % p
  z3 = (z3 * z3)     % p
  z3 = (z3 * x1)     % p
  x2 = (t6 * t7 )    % p
  z2 = (121666 * t5) % p
  z2 = (z2 + t7)     % p
  z2 = (z2 * t5)     % p

  #print("monty result:\n%s\n"%(str((x2,z2,x3,z3))), file=sys.stderr)
  return (x2,z2,x3,z3)

def mladder(xr,sp):
  x1 = xr
  x2 = 1
  z2 = 0
  x3 = xr
  z3 = 1
  for j in range(0,256):
    i = 255 - j
    bit = (sp>>i)&1
    if bit:
      (x3,z3,x2,z2) = ladderstep(x1,x3,z3,x2,z2)
    else:
      (x2,z2,x3,z3) = ladderstep(x1,x2,z2,x3,z3)
  return (x2,z2)

def mladder_opt(xr,sp):
  x1 = xr
  x2 = 1
  z2 = 0
  x3 = xr
  z3 = 1
  prevbit = 0
  for j in range(0,256):
    i = 255 - j
    bit = (sp>>i)&1
    swap = (prevbit != bit)
    # print("py: %i %i %i"%(i,bit,swap),file=sys.stderr)
    prevbit = bit
    if swap:
      (x3,z3,x2,z2) = (x2,z2,x3,z3)
    (x2,z2,x3,z3) = ladderstep(x1,x2,z2,x3,z3)
  if prevbit:
    (x3,z3,x2,z2) = (x2,z2,x3,z3)
  return (x2,z2)

def check_equal(s,a,b):
  a = a % p
  b = b % p
  #print("\n%s:\n%s ==\n%s\n"%(s,str(a),str(b)), file=sys.stderr)
  if not (a == b):
    print("\n%s:\n%s !=\n%s"%(s,str(to_digits(two64,4,a))
                               ,str(to_digits(two64,4,b)))
         , file=sys.stderr)
    print("failed", file=sys.stderr)
    

def test_mladder():
  for s in range(0,999):
    random.seed(s)
    xr = random.getrandbits(512) % p
    random.seed(s+1)
    sp = random.getrandbits(512) % p
    (xr_1, zr_1) = mladder(xr,sp)
    (xr_2, zr_2) = mladder_opt(xr,sp)
    check_equal("xr",xr_1,xr_2)
    check_equal("zr",zr_1,zr_2)

def assert_equal_mladder(xr,sp,xr_r,zr_r,param):
  xr = to_big_int(xr)
  sp = from_digits(two64,sp)
  (xr_s,zr_s) = mladder(xr,sp)
  xr_r = to_big_int(xr_r)
  zr_r = to_big_int(zr_r)
  check_equal("xr",xr_r,xr_s)
  check_equal("zr",zr_r,zr_s)
  return []

def assert_equal_arr(x,y,params):
  #print('>>> assert_equal_arr: x=%s'%(str(x)), file=sys.stderr)
  #print('>>> assert_equal_arr: y=%s'%(str(y)), file=sys.stderr)
  assert(x == y)
  return []

def assert_equal_test(c,params):
  c = to_big_int(c)
  assert(c == 47172631526548581395056365918773001275216341294900259085443495545076823360125)
  return []

def assert_equal_ladderstep_tracing(x1,x2,z2,x3,z3
  ,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16,l17,l18, params):
  x1 = to_big_int(x1)
  x2 = to_big_int(x2)
  z2 = to_big_int(z2)
  x3 = to_big_int(x3)
  z3 = to_big_int(z3)

  l1  = to_big_int(l1)
  l2  = to_big_int(l2)
  l3  = to_big_int(l3)
  l4  = to_big_int(l4)
  l5  = to_big_int(l5)
  l6  = to_big_int(l6)
  l7  = to_big_int(l7)
  l8  = to_big_int(l8)
  l9  = to_big_int(l9)
  l10 = to_big_int(l10)
  l11 = to_big_int(l11)
  l12 = to_big_int(l12)
  l13 = to_big_int(l13)
  l14 = to_big_int(l14)
  l15 = to_big_int(l15)
  l16 = to_big_int(l16)
  l17 = to_big_int(l17)
  l18 = to_big_int(l18)

  (s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18) = ladderstep_tracing(x1,x2,z2,x3,z3)
  check_equal("1",s1,l1)
  check_equal("2",s2,l2)
  check_equal("3",s3,l3)
  check_equal("4",s4,l4)
  check_equal("5",s5,l5)
  check_equal("6",s6,l6)
  check_equal("7",s7,l7)
  check_equal("8",s8,l8)
  check_equal("9",s9,l9)
  check_equal("10",s10,l10)
  check_equal("11",s11,l11)
  check_equal("12",s12,l12)
  check_equal("13",s13,l13)
  check_equal("14",s14,l14)
  check_equal("15",s15,l15)
  check_equal("16",s16,l16)
  check_equal("17",s17,l17)
  check_equal("18",s18,l18)
  return []

def assert_equal_ladderstep(x1,x2,z2,x3,z3,x2_r,z2_r,x3_r,z3_r,params):
  x1 = to_big_int(x1)
  x2 = to_big_int(x2)
  z2 = to_big_int(z2)
  x3 = to_big_int(x3)
  z3 = to_big_int(z3)

  (x2_p,z2_p,x3_p,z3_p) = ladderstep(x1,x2,z2,x3,z3)

  x2_r = to_big_int(x2_r)
  z2_r = to_big_int(z2_r)
  x3_r = to_big_int(x3_r)
  z3_r = to_big_int(z3_r)
 
  check_equal("x2",x2_r,x2_p)
  check_equal("z2",z2_r,z2_p)
  check_equal("x3",x3_r,x3_p)
  check_equal("z3",z3_r,z3_p)
  return []

def mod_p(x,params):
  x = to_big_int(x)
  return to_digits(two64,4,x)

def assert_equal_inv(x,y,params):
  x = to_big_int(x)
  y = to_big_int(y)
  assert(1 == (x*y) % p)
  return []

def scalarmult(u,s):
  sb = encodeLittleEndian(s)
  s  = decodeScalar25519(sb)
  ub = encodeLittleEndian(u)
  u  = decodeUCoordinate(ub)

  x, z = mladder(u,s)
  w = pow(z, p-2, p)
  assert (1 == ((w*z) %p))
  # divide by z
  r = (x * w) % p
  # already packed and freezed
  return (r % p)

def assert_equal_scalarmult(r,u,s,params):
  u = from_digits(two64,u)
  s = from_digits(two64,s)
  r = from_digits(two64,r)
  r_r = scalarmult(u,s)
  check_equal("r=r_r",r,r_r)
  return []

def scalarmult_tracing(u,s):
  sb = encodeLittleEndian(s)
  s  = decodeScalar25519(sb);  l1 = s
  ub = encodeLittleEndian(u)
  u  = decodeUCoordinate(ub);  l2 = u


  x, z = mladder(u,s);         l3 = x; l4 = z
  w = pow(z, p-2, p);          l5 = w
  assert (1 == ((w*z) % p))
  # divide by z
  r = (x * w) % p;             l6 = r
  # already packed and freezed
  return l1,l2,l3,l4,l5,l6,(r % p)

def assert_equal_scalarmult_tracing(r,u,s,l1,l2,l3,l4,l5,l6,params):
  u = from_digits(two64,u)
  s = from_digits(two64,s)
  r = from_digits(two64,r)
  l1 = from_digits(two64,l1)
  l2 = from_digits(two64,l2)
  l3 = from_digits(two64,l3)
  l4 = from_digits(two64,l4)
  l5 = from_digits(two64,l5)
  l6 = from_digits(two64,l6)
  r1,r2,r3,r4,r5,r6,r_r = scalarmult_tracing(u,s)
  check_equal("l1",r1,l1)
  check_equal("l2",r2,l2)
  check_equal("l3",r3,l3)
  check_equal("l4",r4,l4)
  check_equal("l5",r5,l5)
  check_equal("l6",r6,l6)
  check_equal("r=r_r",r,r_r)
  return []

def assert_equal_scalarmult_ref(r,p,s,params):
  p = from_digits(two64,p)
  s = from_digits(two64,s)
  r = from_digits(two64,r)
  #sb = bytearray.fromhex('{:064x}'.format(s))
  pb = bytearray.fromhex('{:064x}'.format(p))
  print("len pb: %s\n"%(str(len(pb))), file=sys.stderr)
  assert (len(pb) == 32)
  Y = bytes_to_element(pb)
  XY = Y.scalarmult(s)
  r1 = XY.to_bytes()
  r2 = int(r1.encode('hex'), 16)
  print("r2: %s\n"%(str(r2)), file=sys.stderr)
  print("r:  %s\n"%(str(r)), file=sys.stderr)
  return []

# * Tests
###########################################################################

if __name__ == "__main__":
  random.seed("random")
  n = random.getrandbits(512) % 2^256
  b = encodeLittleEndian(n)
  n_ = decodeLittleEndian(b)
  assert(n == n_)
  # test_mladder()
