// 32-bit variables

fn test(r.10, r.11 : reg u32) -> reg u32 * reg u32 {
  r.12, r.13, r.14, r.15 : reg u32;
  r.16                   : reg u64;

  cf                     : reg bool;

  r.16 = 7;
  r.12 = 1:u32;
  r.15 = 1:u32;
  cf,r.16 += 42;
  while cf { // original: r13 >= 1
    r.14 = r.11;
    r.13 = r.15;
  }
  
  return r.10, r.12;
}

/*
START:CMD
ARG="typecheck,merge_blocks,save[/tmp/ssa1.mil][info]"
ARG="$ARG,register_liveness[test],local_ssa[test]"
ARG="$ARG,typecheck,save[/tmp/ssa2.mil][info]"
END:CMD
*/

