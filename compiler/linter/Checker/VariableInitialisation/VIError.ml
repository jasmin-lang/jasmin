open Error.CompileError

module VIError (P : sig
  val payload : Jasmin.Prog.var

  val loc : Jasmin.Location.t
end) : CompileError = struct
  type payload = Jasmin.Prog.var

  let payload = P.payload

  let location = P.loc

  (**
  Error code for the variable initialisation error
  *)
  let code = "VI-E001"

  let error_strategy = Error.Recover.Fail

  let to_text fmt () =
      Format.fprintf fmt "Variable %s (declared at : %s) not initialized" payload.v_name
        (Jasmin.Location.tostring payload.v_dloc)
end

let create_vi_error (err_payload : Jasmin.Prog.var) (loc : Jasmin.Location.t) : compile_error
    =
    let module M =
      VIError (struct
        let payload = err_payload

        let loc = loc
      end)
    in
    (module M : CompileError)
