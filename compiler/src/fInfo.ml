open Annotations

type returnaddress_kind =
  | OnStack
  | OnReg

type f_annot = {
    retaddr_kind          : returnaddress_kind option;
    stack_allocation_size : Z.t option;
    stack_size            : Z.t option;
    stack_align           : wsize option;
    max_call_depth        : Z.t option;
    stack_zero_strategy   : (Stack_zero_strategy.stack_zero_strategy * wsize option) option;
    f_user_annot          : annotations;
}

let f_annot_empty = {
    retaddr_kind          = None;
    stack_allocation_size = None;
    stack_size            = None;
    stack_align           = None;
    max_call_depth        = None;
    stack_zero_strategy   = None;
    f_user_annot          = [];
  }

type subroutine_info = { returned_params : int option list }

type call_conv =
  | Export  (** The function should be exported to the outside word *)
  | Subroutine of subroutine_info (** internal function that should not be inlined *)
  | Internal  (** internal function that should be inlined *)

let is_subroutine = function
  | Subroutine _ -> true
  | _            -> false

type t =
  Location.t * f_annot * call_conv * Annotations.annotations list
