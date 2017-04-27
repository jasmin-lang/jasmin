fn foo(reg x : u64, reg y : u64) -> reg u64 {
  x += 1;
  x += y;
  return x;
}

extern fn bar() -> stack u64 * stack u64 {
  reg u1,w1,q1,u2,w2,q2 : u64;
  w1 = 2;
  w2 = 4;
  q1 = 3;
  q2 = 1;
  u1 = foo(w1,q1);
  u2 = foo(w2,q2);
  return u1, u2;
}

fn assert_equal(stack x, y : u64) = python assert_equal;

fn test() {
  stack x1, x2 : u64;
  x1, x2 = bar();
  assert_equal(x1,x2);
}
  
