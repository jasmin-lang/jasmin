// fcond must be bool (FIXME: would be better to point also to decl)

extern fn test(x : reg u64) -> stack u64 {
  y : stack u64;
  y = 42;
  do {
    y += y;
  } while x;
  return x;
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
