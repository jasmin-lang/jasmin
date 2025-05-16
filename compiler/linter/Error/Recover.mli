(**
Error handling strategies for the compiler
*)
type recover_flags = Fail | Recoverable | AlwaysWarn
val recover_flags_of_yojson : Yojson.Safe.t -> recover_flags
val yojson_of_recover_flags : recover_flags -> Yojson.Safe.t
