// macro expansion with missing parameter

param n : u64;
param m : u64;

extern fn test() {
  x : stack u64[m];
  i : inline u64;
  x[0] = 0; 
  for i in 0..$m {
    if $m = 10 {
      x[$m - 1] += 1;
    } else {
      x[$n - 1] -= 1;
    }
  }
}

/*
START:CMD
ARG="typecheck,expand[test][m=10]"
END:CMD
*/
