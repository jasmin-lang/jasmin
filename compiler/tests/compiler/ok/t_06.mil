extern fn test(reg u, v : u64) -> reg u64 * reg u64 {
  reg x1, x2, y1, y2 : u64;
  flag cf : bool;
  x1 = u;         // [0]
  cf,x2 = v + v;  // [1]
  do {            // [2]
    y1 = x1 + x2; // [2,0] 
    x2 = u;       // [2,1]
  } while cf;
  y2 = x2;        // [3]
  do {} while cf; //
  x,y = y2 * x2;  // [4]
  return x, y;    // [-1]  
}
