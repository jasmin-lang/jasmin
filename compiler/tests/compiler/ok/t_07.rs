fn foo0(z : stack u64) -> stack u64 {
  z += z;
  return z;
}

fn foo1(x, y : stack u64, cf : reg bool) -> stack u64 {
  cf,x += y + cf;
  if cf {
    cf, x += y;
    cf, x += y;
  }
  x = foo0(x);
  return x;
}

fn foo2(x, y : stack u64, cf : reg bool) -> stack u64 {
  w : stack u64;
  w = x;
  cf,w += x;
  if !cf {
    cf, x += w;
    cf, x += y;
    x = foo1(x,y,cf);
  }
  return x;
}

/*
START:CMD
ARG="inline[foo2],renumber_reuse,print[input][fun=foo2,info]"
END:CMD
*/
