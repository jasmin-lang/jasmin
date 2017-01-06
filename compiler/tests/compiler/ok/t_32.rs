param n : u64; // use n=2

fn foo(reg x : u64, reg y : u64) -> reg u64 {
  x += 1;
  x += y;
  return x;
}

extern fn bar() -> reg u64 * reg u64 {
  reg u,w,q,ra : u64[n];
  inline i, r1, r2 : u64;

  for i in 0..$n {
    if (i = 0) { w[i] = 2; q[i] = 3; }
    if (i = 1) { w[i] = 4; q[i] = 1; }
    u[i] = foo(w[i],q[i]);
  }
  ra := u;
  r1 = ra[0];
  r2 = ra[1];
  return r1, r2;
}

fn assert_equal(stack x, y : u64) = python assert_equal;

fn test() {
  reg x1, x2 : u64;
  x1, x2 = bar();
  assert_equal(x1,x2);
}
