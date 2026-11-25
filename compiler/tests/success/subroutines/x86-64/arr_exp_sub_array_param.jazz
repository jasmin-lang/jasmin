fn f (reg u32[2] x) -> reg u32 {
  reg u32 res;
  res = x[1];
  return res;
}

export fn main () -> reg u32 {
  reg u32[3] s;

  reg u32 res;
  res = 0;

  inline int i;
  for i = 0 to 3 {
    s[i] = res;
  }

  res = f(s[1:2]);

  return res;
}
