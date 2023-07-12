require import CoreInt JWord.

abstract theory SLH.
  type msf_t.
  op of_int : int -> msf_t.

  abbrev [-printing] init_msf : msf_t = of_int 0.

  (* FIXME ec *)
  (* abbrev [-printing] move_msf (msf:msf_t) : msf_t = msf. *)
  (* abbrev. body cannot reduce to a variable *)
  op mov_msf (msf : msf_t) : msf_t = msf.

  op protect_8   (x : W8  .t) (msf : msf_t) : W8  .t = x.
  op protect_16  (x : W16 .t) (msf : msf_t) : W16 .t = x.
  op protect_32  (x : W32 .t) (msf : msf_t) : W32 .t = x.
  op protect_64  (x : W64 .t) (msf : msf_t) : W64 .t = x.
  op protect_128 (x : W128.t) (msf : msf_t) : W128.t = x.
  op protect_256 (x : W256.t) (msf : msf_t) : W256.t = x.
  op protect_ptr (x : 'a) (msf : msf_t) : 'a = x.

  op update_msf (b:bool) (msf : msf_t) : msf_t =
    if b then msf else of_int (CoreInt.opp 1).

end SLH.

clone SLH as SLH64 with
   type msf_t = W64.t,
   op of_int <- W64.of_int.

clone SLH as SLH32 with
   type msf_t = W32.t,
   op of_int <- W32.of_int.




