// use undeclared parameter

fn test(x : stack u64) -> stack u64 {
  x += $undef_param;
  return x;
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
