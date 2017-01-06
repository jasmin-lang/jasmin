extern fn test(reg u_in, v_in : u64) -> reg u64 * reg u64 {
  reg x, y : u64;
  reg x_out, y_out : u64;
  reg u, v : u64;
  stack z : u64;
  flag cf : bool;

  u = u_in;
  v = v_in;
  z = u_in;
  cf,y = u + v;

  x := y;

  y,x = u * v;
  y = x;
  x = v;
  cf,y = x + y;

  // do {
  //   x = u;
  //   y = x;
  //   x = v;
  //   cf,y = x + y;
  // } while cf;
  // y = x;
  // x = u;
  // y = x;
  // x = v;
  // cf,y = x + y;

  if cf {
    x = v;
    y = x + y;    
  } else {
    x = y + x;
    x = u;
    z = y;
  }
  y = y + z;
  x = x + y;
  y = x;
  x = v;
  cf,y = x + y;
  x_out = x;
  y_out = y;
  return x_out, y_out;
}
