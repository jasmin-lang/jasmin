extern fn test(reg u_in : u64) -> reg u64 {
  reg i, x, x_out : u64;
  stack a : u64[20];
  stack i_s : u64;
  flag cf : bool;
  
  i = 10;
  do {
    x = a[i];
    i_s = i;
    x = x + 1;
    i = i_s;
    cf,i = i - 1;
  } while !cf;

  x_out = u_in;
  x_out += x;
  return x_out;
}
