open Leakage

val pp_leak_i : Format.formatter -> leak_i -> unit

val pp : 'info Conv.coq_tbl -> Format.formatter -> leak_f_tr list * leak_f_lf_tr -> unit
