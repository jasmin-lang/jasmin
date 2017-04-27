extern fn bar(reg u, v : u64) -> reg u64 * reg u64 {
  reg x, y : u64;
  x = u * v;
  y = u + v;
  x = x * u;
  y = y + v;
  return x, y;
}  
