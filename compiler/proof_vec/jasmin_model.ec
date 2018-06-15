require import Int.

(*sopn_tin, sopn_tout*)
type global_mem_t.
abstract theory W.

type t.
op size : int.
op (+)    : t -> t -> t.
op (-)    : t -> t -> t.
op [-]    : t -> t.
op (`&`)  : t -> t -> t.
op (%)    : t -> t -> t.
op ( * )  : t -> t -> t.
op (/)    : t -> t -> t.
op ( & )  : t -> t -> t.
op (`|`)    : t -> t -> t.
op (|>>)  : t -> t -> t.
op (`<`)    : t -> t -> bool.
op (<=)   : t -> t -> bool.
op (`^`)  : t -> t -> t.
 
op of_int: int -> t.
end W.

(* example below *)

theory W8.
  clone include W with op size = 8.
  op (`>>`) :  t -> t -> t. 
  op (`<<`) : t -> t -> t.
  op addc_8: t -> t -> bool -> (bool * t).
end W8.
export W8. 
 
theory W16.
  clone include W with op size = 16.
  op (`>>`) :  t -> W8.t -> t. 
  op (`<<`) : t -> W8.t -> t.
  op addc_16: t -> t -> bool -> (bool * t).
end W16. 
export W16.

theory W32.
  clone include W with op size = 32.
  op (`>>`) :  t -> W8.t -> t. 
  op (`<<`) : t -> W8.t -> t.
  op addc_32: t -> t -> bool -> (bool * t).
end W32.
export W32.

theory W64.
  clone include W with op size = 64.
  op (`>>`) :  t -> W8.t -> t. 
  op (`<<`) : t -> W8.t -> t.
  op mulu_64: t -> t -> (t*t).
  op addc_64: t -> t -> bool -> (bool * t).
end W64. 
export W64.

theory W128.
  clone include W with op size = 128.
  op (`>>`) :  t -> W8.t -> t. 
  op (`<<`) : t -> W8.t -> t.
  op addc_128: t -> t -> bool -> (bool * t).
end W128. 
export W128.

theory W256.
  clone include W with op size = 256.
  op (`>>`) :  t -> W8.t -> t. 
  op (`<<`) : t -> W8.t -> t.
  op addc_256: t -> t -> bool -> (bool * t).
  op cast_32: t -> W32.t.
end W256. 
export W256.

op sigext_8_8:   W16.t -> W8.t.
op sigext_8_16:  W16.t -> W16.t.
op sigext_8_32:  W16.t -> W32.t.
op sigext_8_64:  W16.t -> W64.t.
op sigext_8_128: W16.t -> W128.t.
op sigext_8_256: W16.t -> W256.t.

op sigext_16_8:   W16.t -> W8.t.
op sigext_16_16:  W16.t -> W16.t.
op sigext_16_32:  W16.t -> W32.t.
op sigext_16_64:  W16.t -> W64.t.
op sigext_16_128: W16.t -> W128.t.
op sigext_16_256: W16.t -> W256.t.

op sigext_32_8:   W32.t -> W8.t.
op sigext_32_16:  W32.t -> W16.t.
op sigext_32_32:  W32.t -> W32.t.
op sigext_32_64:  W32.t -> W64.t.
op sigext_32_128: W32.t -> W128.t.
op sigext_32_256: W32.t -> W256.t.

op sigext_64_8:   W64.t -> W8.t.
op sigext_64_16:  W64.t -> W16.t.
op sigext_64_32:  W64.t -> W32.t.
op sigext_64_64:  W64.t -> W64.t.
op sigext_64_128: W64.t -> W128.t.
op sigext_64_256: W64.t -> W256.t.

op sigext_128_8:   W128.t -> W8.t.
op sigext_128_16:  W128.t -> W16.t.
op sigext_128_32:  W128.t -> W32.t.
op sigext_128_64:  W128.t -> W64.t.
op sigext_128_128: W128.t -> W128.t.
op sigext_128_256: W128.t -> W256.t.

op sigext_256_8:   W256.t -> W8.t.
op sigext_256_16:  W256.t -> W16.t.
op sigext_256_32:  W256.t -> W32.t.
op sigext_256_64:  W256.t -> W64.t.
op sigext_256_128: W256.t -> W128.t.
op sigext_256_256: W256.t -> W256.t.


op loadW32: global_mem_t -> W64.t -> W32.t.
op storeW32: global_mem_t -> W64.t -> W32.t -> global_mem_t.

op x86_MOVD_32: W32.t -> W128.t.
op x86_ROL_32: W32.t -> W8.t -> (bool * bool * W32.t).


op loadW64: global_mem_t -> W64.t -> W64.t.
op storeW64: global_mem_t -> W64.t -> W64.t -> global_mem_t.

op x86_SHLD_64: W64.t -> W64.t -> W8.t -> (bool * bool * bool * bool * bool * W64.t).
op x86_SHRD_64: W64.t -> W64.t -> W8.t -> (bool * bool * bool * bool * bool * W64.t).

op loadW128: global_mem_t -> W64.t -> W128.t.
op storeW128: global_mem_t -> W64.t -> W128.t -> global_mem_t.

op x86_VPSLL_4u32: W128.t -> W8.t -> W128.t.
op x86_VPSRL_4u32: W128.t -> W8.t -> W128.t.
op x86_VPSHUFB_128: W128.t -> W128.t -> W128.t.
op x86_VPSHUFD_128: W128.t -> W8.t -> W128.t.



