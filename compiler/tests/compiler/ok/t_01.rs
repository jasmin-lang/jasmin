param n : u64;

// we can use a variable name that is ignored
fn foo1(x : stack u64) -> stack u64 * reg u64 * reg bool;

// we can also leave out variable names
fn foo2(stack u64, stack u64[n], x,x,x : stack u64) -> stack u64[n] =
  python print_foo;

// nothing
fn foo3(_x : stack u64) {
}

// decl only
fn foo4(_x : stack u64) {
  _y : stack u64; // will not be printed
}

// body only
fn foo5(x : stack u64) {
  x += x;
}

// return only
fn foo6(x : stack u64) -> stack u64 {
  return x;
}

// deck + body
fn foo7(x : stack u64) {
  y : stack u64;
  x += y;
}

// deck + return
fn foo8(x : stack u64) -> stack u64 * stack u64 {
  y : stack u64;
  return y, x;
}

// body + return
fn foo9(x : stack u64) -> stack u64 {
  x += x;
  return x;
}

// decl + body + return
fn foo10(x, y : stack u64, z : reg bool) -> stack u64 {
  w : stack u64;
  w = x;
  w += x;
  if (w = 5) {
    z, x += w;
    z, x += y;
  }
  return x;
}

/*
START:CMD
ARG="print[input][types]"
END:CMD
*/
