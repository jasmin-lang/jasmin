open Global
open Wsize
open Prog

type pmap

type param_info = {
    pi_ptr      : var;
    pi_writable : bool;
    pi_align    : wsize;
  }

type stk_alloc_oracle_t =
  { sao_has_stack : bool
  ; sao_calls  : Sf.t
  ; sao_params : param_info option list (* Allocation of pointer params *)
  ; sao_return : int option list        (* Where to find the param input region *)
  ; sao_alloc  : pmap                   (* info to finalize stack_alloc *)
  }

val alloc_prog: 'info prog -> pmap * (stk_alloc_oracle_t * 'info func) list

type pos_kind =
  | Pstack of int * wsize
  | Pregptr of var
  | Pstkptr of int

val alloc_stack: pmap -> var list -> (var * pos_kind) list * int * wsize * int list
val alloc_mem: pmap -> (var * glob_value) list -> Obj.t list * (var * (int * wsize)) list
