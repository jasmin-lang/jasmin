fn f (reg u32[3] x) -> reg u32[1] {
  reg u32[1] res;
  res[0] = x[1];
  return res;
}

export fn main () -> reg u32 {
  reg u32[3] s;

  reg u32[2] r;

  reg u32 res;
  res = 0;

  inline int i;
  for i = 0 to 3 {
    s[i] = res;
  }

  r[0:1] = f(s);
  res = r[0];

  return res;
}
