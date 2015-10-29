(* * Typing and well-formedness of IL *)

(*

We should perform the following checks:
1. All variables that are read must be defined.
2. For carry flags, every arithmetic operation 
   makes previously written carry-flag variables
   undefined.
3. ...
4. ensure that LHS "h l = ..." in mul distinct
5. ensure that src1 and dest equal for X64
*)

let efuns_type (_efun : IL_Lang.efun_ut list) : IL_Lang.efun list =
  failwith "undefined"

let efun_type (_efun : IL_Lang.efun_ut) : IL_Lang.efun =
  failwith "undefined"
