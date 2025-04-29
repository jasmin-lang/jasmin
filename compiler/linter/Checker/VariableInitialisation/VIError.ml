open Error

let create_vi_error (err_payload : Jasmin.Prog.var) (loc : Jasmin.Location.t) : CompileError.t
    =
    {
      location = loc;
      error_strategy = Error.Recover.Fail;
      code = "VI-E001";
      to_text =
       fun fmt () -> Format.fprintf fmt "Variable %s (declared at : %s) not initialized" err_payload.v_name (Jasmin.Location.tostring err_payload.v_dloc)
    }
