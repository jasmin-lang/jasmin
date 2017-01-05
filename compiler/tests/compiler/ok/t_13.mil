// macro expansion

param n : u64;
param m : u64;

extern fn test() {
  arr1, arr2 : stack u64[2 * n];
  arr3, arr4 : stack u64[2 * m];
  cf : reg bool;
  i : reg u64;
  
  while cf {
    if cf {
      arr1 := arr2; 
      arr3 = arr4;
      arr3[i] = arr4[2];
    }
  }
  arr1 := arr2; 
  arr3 = arr4;
}

/*
START:CMD
ARG="renumber_fun_unique,typecheck,expand[test][n=7,m=8],array_assign_expand[test]"
ARG="$ARG,array_expand[test]"
ARG="$ARG,typecheck,print[renum][]"
END:CMD
*/
