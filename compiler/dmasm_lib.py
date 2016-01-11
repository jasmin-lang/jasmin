from __future__ import print_function
import sys
import logging
import random

sys.ps1 = ""

# * Classes for prime field arithmetic
###########################################################################




# * Functions callable from dmasm
###########################################################################

def confirm_started():
  print("done", file=sys.stdout)

def print_u64_arr(x,params):
  print('>>> print_u64_arr: x=%s'%(str(x)), file=sys.stderr)
  print('>>> print_u64_arr: n=%s'%(str(params['n'])), file=sys.stderr)
  return []

def print_u64(x,params):
  print('%s '%(str(x)), file=sys.stderr, end="")
  return []

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

# * Functions for 25519 with 4 limbs
###########################################################################

p = 2**255 - 19
two64 = 2**64

def to_big_int(n):
  return from_digits(two64,n)

def rand(s,params):
  print('>>> rand_arr: x=%s'%(str(s)), file=sys.stderr)
  random.seed(s)
  n = random.getrandbits(512) % p
  res = to_digits(two64,4,n)
  print('>>> rand_arr: res=%s'%(str(res)), file=sys.stderr)
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
def monty(x1, x2, z2, x3, z3):
  print("monty input:\n%s\n"%(str((x1,x2,z2,x3,z3))), file=sys.stderr)
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

  print("monty result:\n%s\n"%(str((x2,z2,x3,z3))), file=sys.stderr)
  return (x2,z2,x3,z3)

def monty_test():
  t1       = x2 + z2
  t2       = x2 - z2
  t7       = t2 * t2;
  t7_p[..]     = t7[..];
  t6[..]       = square(t1[..]);
  t6_p[..]     = t6[..];
  t5[..]       = t6[..];
  t5[..]       = sub(t5[..], t7[..]);
  t5_p[..]     = t5[..];
  t6[..]       = x3;
  t7[..]       = t6[..];
  t6[..]       = add(t6[..], z3);
  t7[..]       = sub(t7[..], z3);
  t3_p[..]     = t6[..];
  t4_p[..]     = t7[..];
  t9[..]       = mul(t3_p, t2);
  t9_p[..]     = t9[..];
  t8[..]       = mul(t4_p, t1);
  w1[..]       = t8[..];
  t8[..]       = add(t8[..], t9_p);
  w1[..]       = sub(w1[..], t9_p);
  x3           = t8[..];
  z3           = w1[..];
  w2[..]       = square(x3);
  x3           = w2[..];
  w3[..]       = square(z3);
  z3           = w3[..];
  w4[..]       = mul(z3,x1);
  z3           = w4[..];
  w5[..]       = mul(t6_p, t7_p);
  x2           = w5[..];
  w6[..]       = mul(t5_p, c121666_p);   /* FIXME: specialize */
  w6[..]       = add(w6[..], t7_p);
  x2           = w6[..];
  w7[..]       = mul(z2, t5_p);
  z2           = w7[..];



def assert_equal_ladderstep(x1,x2,z2,x3,z3,x2_r,z2_r,x3_r,z3_r,params):
  x1 = to_big_int(x1)
  x2 = to_big_int(x2)
  z2 = to_big_int(z2)
  x3 = to_big_int(x3)
  z3 = to_big_int(z3)

  (x2_p,z2_p,x3_p,z3_p) = monty(x1,x2,z2,x3,z3)

  x2_r = to_big_int(x2_r)
  z2_r = to_big_int(z2_r)
  x3_r = to_big_int(x3_r)
  z3_r = to_big_int(z3_r)
  
  print("\n%s ==\n%s\n"%(str(x2_r),str(x2_p)), file=sys.stderr)
  assert (x2_r == x2_p)
  print("\n%s ==\n%s\n"%(str(z2_r),str(z2_p)), file=sys.stderr)
  assert (z2_r == z2_p)
  print("\n%s ==\n%s\n"%(str(x3_r),str(x3_p)), file=sys.stderr)
  assert (x3_r == x3_p)
  print("\n%s ==\n%s\n"%(str(z3_r),str(z3_p)), file=sys.stderr)
  assert (z3_r == z3_p)
  return []

# * Tests
###########################################################################

if __name__ == "__main__":
  rand_25519(1)

  # test from_digits
  random.seed(1)
  n = random.getrandbits(512) % p25519
  res = to_digits(two64,4,n)
  assert (from_digits(two64,res) == n)

  
  
