// macro expansion

param n : u64;
param m : u64;

extern fn test() {

  cf            : reg bool;
  ptr           : reg u64;
  v_14           : stack u64[n];
  v_0           : stack u64[n];
  v_inner       : stack u64[n];
  v_inner_outer : stack u64[n];
  v_inner_inner : stack u64[m];
  v_dead        : stack u64[m];
  i, j          : inline u64;

  if cf {
    v_0[0] = 0; 
    for i in 10..$n {
      if $n = 15 {
        v_14[$n - 1] += 1;
        v_inner[i] = i;
        for j in 5..$m {
          v_inner_outer[i] = MEM[ptr + i*8];
          v_inner_inner[j] = j;
          MEM[ptr + j*8] = j;
        }
      } else {
        v_dead[$n - 1] -= 1;
      }
    }
  }
}

/*
START:CMD
ARG="renumber_fun_unique,typecheck,expand[test][n=15,m=7],renumber_reuse,print[renum][]"
END:CMD
*/
