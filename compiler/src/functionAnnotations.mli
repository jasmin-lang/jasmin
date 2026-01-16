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
