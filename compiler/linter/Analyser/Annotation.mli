
(**
    Annotation type.
    Used to wrap domain with a minimal [Empty] value.
*)
type 'domain annotation = Empty | Annotation of 'domain


(**
    Pretty printer wraper function for the annotation type following [Jasmin.Printer.pp_iprog] interface.
*)
val pp :
  (Format.formatter -> Jasmin.Location.i_loc * 'domain -> unit) ->
  Format.formatter -> Jasmin.Location.i_loc * 'domain annotation -> unit

(**
    Wrapper for domain merge functions. [merge a Empty f]
*)
val merge :
  'domain annotation -> 'domain annotation -> ('domain -> 'domain -> 'domain) -> 'domain annotation

(**
    Inclusion test for annotations. [included a b f] return :
    - true if [a] is [Empty]
    - false if [b] is [Empty] and [a] is not [Empty]
    - true if inner domain [a] is included in inner domain [b] according to the function [f] otherwise
*)
val included : 'domain annotation -> 'domain annotation -> ('domain -> 'domain -> bool) -> bool

(**
    [bind a f] applies the function [f] to the value contained in the annotation [a] and return a new annotation. If [a] is [Empty], it returns [Empty].
*)
val bind : 'domain annotation -> ('domain -> 'domain annotation) -> 'domain annotation

(**
    Unwrapping function for annotation. It should only be used on annotations that are not [Empty]. It will otherwise raise an [Invalid_argument] exception.
*)
val unwrap : 'domain annotation -> 'domain

(**
    [map a f] applies the function [f] to the value contained in the annotation [a]. If [a] is [Empty], it returns [Empty].
*)
val map : 'a annotation -> ('a -> 'b) -> 'b annotation
