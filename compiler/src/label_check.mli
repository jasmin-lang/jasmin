open Prog


(**
Record types describing data used to detect and print informations about function labels. Used for error (warning) printing
*)
type function_label = {
  loc : L.t;
  fname : string;
}

(**
Duplicate label error (warning) containing informations about the two conflicting functions
*)
type duplicate_label_warn = {
  first_decl : function_label;
  conflict_decl : function_label;
}

(** 
Function that print a duplicate_label_warn using Utils.warning
@param error : duplicate_label_warn
*)
val warn_duplicate_label : duplicate_label_warn -> unit

(**
Check if functions have conflicting names when translated to their assembly label names.
It return the list of conflict errors detected.
The way error are handled is let to the calling function.
@param prog : program to check
@return : duplicate_label_warn list 
*)
val get_labels_errors : ('len,'info,'asm) gprog -> duplicate_label_warn list