extern fn test() {
  stack arr : u64[4];
  reg i, x  : u64;
  x = arr[i + i]; 
   // ERROR: array expansion: the parameter-expression i + i cannot be used as index
}
