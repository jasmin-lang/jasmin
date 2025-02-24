open Wsize
open Prog

type alignment_constraint =
  { ac_strict: wsize
  ; ac_heuristic: wsize }

type param_info = {
    pi_ptr      : var;
    pi_writable : bool;
    pi_align    : alignment_constraint;
  }

type ptr_kind = 
  | Direct   of var * Interval.interval * Expr.v_scope
  | StackPtr of var 
  | RegPtr   of var  

type stk_alloc_oracle_t =
  { sao_calls  : Sf.t
  ; sao_params : param_info option list (* Allocation of pointer params *)
  ; sao_return : int option list        (* Where to find the param input region *)
  ; sao_slots  : (var * wsize * int) list 
  ; sao_align : wsize
  ; sao_size  : int               (* Not normalized with respect to sao_local_align *)
  ; sao_alloc : ptr_kind Hv.t
  ; sao_modify_rsp : bool
  }

type glob_alloc_oracle_t = 
  { gao_data : Obj.t list         (* word u8 *)
  ; gao_slots  : (var * wsize * int) list 
  ; gao_align : wsize
  ; gao_size  : int               (* Not normalized with respect to sao_local_align *)
  }


val alloc_stack_prog : var Arch_full.callstyle -> Wsize.wsize -> ('info, 'asm) prog -> glob_alloc_oracle_t * stk_alloc_oracle_t Hf.t

val extend_sao : stk_alloc_oracle_t -> var list -> int * wsize * (var * int) list
 
