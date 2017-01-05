fn foo1(x, y : stack u64, z : reg bool) -> stack u64 {
  w : stack u64;
  w = x;
  w += x;
  if (w = 5) {
    z, x += w;
    z, x += y;
  }
  return x;
}

fn foo2(x, y : stack u64, z : reg bool) -> stack u64 {
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
ARG="renumber_module_unique,print[input][types]"
END:CMD
*/
