(* -------------------------------------------------------------------- *)
type symbol = string
type pident = symbol Location.located

(* -------------------------------------------------------------------- *)
type wsize = [ `W8 | `W16 | `W32 | `W64 | `W128 | `W256 ]

(* -------------------------------------------------------------------- *)
type simple_attribute =
  | Aint    of Z.t
  | Aid     of symbol
  | Astring of string
  | Aws     of wsize
  | Astruct of annotations

and attribute = simple_attribute Location.located

and annotation = pident * attribute option

and annotations = annotation list
