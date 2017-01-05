extern fn test(reg u_in, v_in : u64) -> reg u64 {
  reg x : u64[20];
  reg z_out : u64;
  inline i : u64;

  
  x[0] = u_in;
  x[1] = v_in;
  for i in 2..10 {
    x[i] = i;
  }

  for i in 0..10 {
    x[i] += x[i];
  }

  z_out = 0;
  for i in 0..10 {
    z_out += x[i];
  }

  return z_out;
}
