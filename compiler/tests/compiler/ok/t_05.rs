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

/*
START:CMD
ARG="merge_blocks,print[input][types,info]"
END:CMD
*/
