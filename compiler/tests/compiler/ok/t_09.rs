// reuse the same number for different names, renumber before
//   type checking

extern fn test(x.1, y.1 : stack u64) -> stack u64 {
  x.1 += y.1;
  return x.1;
}

/*
START:CMD
ARG="typecheck,print[renum][fun=test]"
END:CMD
*/
