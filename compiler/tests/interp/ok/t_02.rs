fn rand_u64(reg u64) -> reg u64 = python rand_u64;
fn assert_equal_u64(reg u64, reg u64) = python assert_equal_u64;

fn helper() {
  x, y, z   : reg u64;
  w, r1, r2 : reg u64;
  s         : reg u64;

  s = 42;

  x = rand_u64(s); s += 1;
  y = rand_u64(s); s += 1;
  z = rand_u64(s);

  r1 = x*z;
  w  = y*z;
  r1 += w;

  r2 = x + y;
  r2 *= z;

  assert_equal_u64(r1,r2);
}

fn test() {
  helper();
}

/*
START:CMD
ARG="typecheck,renumber_fun_unique,interp[][][test][]"
END:CMD
*/
