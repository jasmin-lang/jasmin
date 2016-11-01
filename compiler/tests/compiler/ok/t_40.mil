extern fn test(reg x_in : u64) -> reg u64 {
  reg x, y, z1, z2, x_out : u64;
  flag cf : bool;

  z1 = 5;
  x = x_in;
  y = 10;
  do {
    x += z1;
    y += 1;
  } while !cf;
  
  if cf {
    x = z1;
  } else {
    x = z2;
  }

  x += y;
  x += x;
  x_out = x;
  return x_out;
}
