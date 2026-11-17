With [-dit] or [#[dit]], an armv8a export function sets PSTATE.DIT for its
body and restores the caller's value; [#[dit=no]] opts out.

  $ F=success/armv8a/dit.jazz

  $ ../jasminc -arch armv8a -system linux $F -o dit.s
  $ sed -n '/^dit_add:/,/ret$/p' dit.s | tr '\t' ' '
  dit_add:
   str  x30, [sp, #-16]!
   mrs  x16, s3_3_c4_c2_5
   str  x16, [sp, #-16]!
   mov  x16, #0x1000000
   msr  s3_3_c4_c2_5, x16
   dsb  sy
   isb
   bl   .Ladd$1
  .Ldit_add$1:
   ldr  x16, [sp], #16
   msr  s3_3_c4_c2_5, x16
   ldr  x30, [sp], #16
   ret
  $ sed -n '/^no_dit_add:/,/ret$/p' dit.s | tr '\t' ' '
  no_dit_add:
   str  x30, [sp, #-16]!
   add  x0, x0, x1
   ldr  x30, [sp], #16
   ret

  $ ../jasminc -arch armv8a -system linux -dit $F -o all.s
  $ grep -E '^[[:alnum:]_]*:$|mrs' all.s | tr '\t' ' '
  dit_randombytes:
   mrs  x16, s3_3_c4_c2_5
  dit_stack_zero:
   mrs  x16, s3_3_c4_c2_5
  plain_add:
   mrs  x16, s3_3_c4_c2_5
  no_dit_add:
  dit_add:
   mrs  x16, s3_3_c4_c2_5
  add:
