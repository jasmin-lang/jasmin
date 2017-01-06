// use indexed variables

fn foo(z.1, z.2 : stack u64) -> stack u64 {
  z.1 += z.2;
  return z.1;
}

/*
START:CMD
ARG="print[input][fun=foo,info]"
END:CMD
*/
