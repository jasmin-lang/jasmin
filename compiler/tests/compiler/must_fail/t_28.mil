// ill-typed addition

extern fn test(x : reg u64, y : reg u64[4]) -> reg u64 {
  x += y[0];    // this one is correct
  y[1] += y[0]; // this one too
  y[2] += x;    // this one too
  x += y;       // this is the problem
  return x;
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
