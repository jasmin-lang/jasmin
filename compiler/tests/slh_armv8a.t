Lowering of the selective speculative load hardening operators on ARMv8-A:
the barriers, and the conditions of the updates after each branch.

  $ cat > slh.jazz << EOF
  > export fn slh(reg u64 x y p, reg u32 z) -> reg u64 {
  >   reg u64 msf m r i;
  >   reg bool b;
  >   msf = #init_msf();
  >   b = x < y;
  >   r = 0;
  >   if (b) {
  >     msf = #update_msf(b, msf);
  >     r = [p + 8 * x];
  >     m = #mov_msf(msf);
  >     r = #protect(r, m);
  >   } else {
  >     msf = #update_msf(!b, msf);
  >   }
  >   i = 0;
  >   while { b = i <s y; } (b) {
  >     msf = #update_msf(b, msf);
  >     i += 1;
  >   }
  >   msf = #update_msf(!b, msf);
  >   z = #protect_32(z, msf);
  >   [:u32 p] = z;
  >   return r;
  > }
  > EOF
  $ ../jasminc -arch armv8a -system linux -o slh.s slh.jazz
  $ awk '/^\.L/ { print } $1 ~ /^(dsb|isb|csdb|movn|b\.[a-z]+)$/ { print $1 } $1 == "orr" { print $1, substr($2, 1, 1) } $1 == "csel" { print $1, $NF }' slh.s
  dsb
  isb
  b.cc
  movn
  csel cs
  .Lslh$3:
  movn
  csel cc
  orr x
  csdb
  .Lslh$4:
  .Lslh$2:
  movn
  csel lt
  .Lslh$1:
  b.lt
  movn
  csel ge
  orr w
  csdb
