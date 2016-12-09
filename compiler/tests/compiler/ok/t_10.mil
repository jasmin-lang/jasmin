// check that types propagated to all parameter occurences

param n : u64;

extern fn test() {
  x : stack u64[n];
  i : inline u64;
  x[0] = 0; 
  for i in 0..$n {
    if ($n = 10 && $n = 10) || false { // test || and &&
      x[$n - 1 ] += 1;
    } else {
      x[$n - 1] += 1;
    }
  }
}

/*
START:CMD
ARG="print[renum][types]"
END:CMD
*/
