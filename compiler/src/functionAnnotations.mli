val pannot_to_annotations : Syntax.pannotations -> Annotations.annotations
(** Remove expressions from annotations. Raises [HiError] when it encounters too
    complex expressions. *)

val process_f_annot :
  Location.t ->
  string ->
  FInfo.call_conv ->
  Syntax.pannotations ->
  FInfo.f_annot
(** Extracts a few well-known attributes from the annotation of a function. *)

val get_required_alignment : _ Prog.gfunc -> Wsize.wsize Utils.Ms.t
(** Extracts the required alignment for each function argument. Reads the
    function annotations first then defaults to U8 for export functions (no
    requirement for non-export functions). *)
