// wrong return storage type

extern fn test(x : reg u64) -> stack u64 {
  return x;
}

/*
START:CMD
ARG="typecheck"
END:CMD
*/
