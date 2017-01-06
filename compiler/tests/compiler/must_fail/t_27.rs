// ill-typed addition

extern fn test(x : reg u64, y : reg bool) -> reg u64 {
  x += y;
  return x;
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
