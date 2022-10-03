type subroutine_info = { returned_params : int option list }

type call_conv =
  | Export  (** The function should be exported to the outside word *)
  | Subroutine of subroutine_info (** internal function that should not be inlined *)
  | Internal  (** internal function that should be inlined *)

type t =
  Location.t * Annotations.f_annot * call_conv * Annotations.annotations list
