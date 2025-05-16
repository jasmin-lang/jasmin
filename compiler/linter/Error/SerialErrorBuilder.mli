
(**
Complementary module for [CompileError].
The main purpose of this module is to provide a way to serialize errors in JSON format using yojson library
*)


(**
proxy type for [Jasmin.Location.t]
it is used to use ppx for json serialization, it allows jasmin to not depend on yojson. It will probably be removed in the future.
We use the preprocesssor ppx_yojson_conv to generate the yojson serialization functions easily.
*)
type loc = {
  loc_fname : string;
  loc_start : int * int;
  loc_end : int * int;
  loc_bchar : int;
  loc_echar : int;
}

(**
proxy [loc] type builder function :
args : [Jasmin.Location.t]
return : [loc]
*)
val location_to_loc : Jasmin.Location.t -> loc

(**
proxy record type for [CompileError.CompileError] first class module. It is used to serialize the error in JSON format.
*)
type error_payload = {
  message : string;
  location : loc;
  error_strategy : Recover.recover_flags;
  code : string;
}

(**
 Type [error_payload] builder function :
args : [CompileError.CompileError]
return : [error_payload]
*)
val build_payload : (module CompileError.CompileError) -> error_payload

(**
bulk serializer function for [error_payload] type. Write errors given as argument to a formatter.
args :
* [Format.formatter] : the formatter to use for the serialization
* [error_payload list] : the list of error_payload to serialize
return : [unit]
*)
val serialize_errors : Format.formatter -> error_payload list -> unit
