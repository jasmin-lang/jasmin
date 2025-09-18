require import List.

(* Values are declassified via an opaque type *)
type declassified_value.

type decl = [
  | DeclBase of declassified_value
  | DeclNode of decl & decl
  | DeclEmpty
].

(* Declassified values have some unspecified encoding *)
op to_decl : 'a -> decl.

type decls = decl list.
