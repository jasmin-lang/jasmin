open Utils
open Prog
module L = Location

let is_array_copy (x:lval) (e:expr) =
  match x with
  | Lvar x ->
    let x = L.unloc x in
    begin match x.v_ty with
    | Arr (xws, xn) ->
      begin match e with
      | Pvar y ->
        let y = L.unloc y.gv in
        begin match y.v_ty with
        | Arr(yws, yn) ->
           (* Ignore ill-typed copies: they are later rejected by “typing”. *)
           if arr_size yws yn < arr_size xws xn then None else
           if x.v_kind = Reg(Normal, Direct) then Some (xws, xn)
           else if y.v_kind = Reg(Normal, Direct) then Some (yws, arr_size xws xn / size_of_ws yws)
           else None
        | _ -> None
        end
      | _ -> None
      end
    | _ -> None
    end
  | _ -> None

let rec iac_stmt pd is = List.map (iac_instr pd) is
and iac_instr pd i = { i with i_desc = iac_instr_r pd i.i_loc i.i_desc }
and iac_instr_r pd loc ir =
  match ir with
  | Cassgn (x, t, _, e) ->
    if !Glob_options.introduce_array_copy then 
      match is_array_copy x e with
      | None -> ir
      | Some (ws, n) -> 
          warning IntroduceArrayCopy 
            loc "an array copy is introduced";
          let op = Pseudo_operator.Ocopy(ws, Conv.pos_of_int n) in
          Copn([x], t, Sopn.Opseudo_op op, [e])
    else ir
  | Cif (b, th, el) -> Cif (b, iac_stmt pd th, iac_stmt pd el)
  | Cfor (i, r, s) -> Cfor (i, r, iac_stmt pd s)
  | Cwhile (a, c1, t, c2) -> Cwhile (a, iac_stmt pd c1, t, iac_stmt pd c2)
  | Copn (xs,t,o,es) ->

    begin match o, xs with
    | Sopn.Opseudo_op(Pseudo_operator.Ospill(o,_)), _ ->
      let tys = List.map (fun e -> Conv.cty_of_ty (Typing.ty_expr pd loc e)) es in  
      Copn(xs,t, Sopn.Opseudo_op(Pseudo_operator.Ospill(o, tys)), es)
                 
    | Sopn.Opseudo_op(Pseudo_operator.Ocopy(ws, _)), [Lvar x] ->
      (* Fix the size it is dummy for the moment *)
      let xn = size_of (L.unloc x).v_ty in
      let wsn = size_of_ws ws in
      if xn mod wsn <> 0 then 
        Typing.error loc 
          "the variable %a has type %a, its size (%i) should be a multiple of %i"
          (Printer.pp_var ~debug:false) (L.unloc x)
          PrintCommon.pp_ty (L.unloc x).v_ty
          xn wsn
      else
        let op = Pseudo_operator.Ocopy (ws, Conv.pos_of_int (xn / wsn)) in
        Copn(xs,t,Sopn.Opseudo_op op, es)
    | Sopn.Opseudo_op(Pseudo_operator.Oswap _), x::_ ->
      (* Fix the type it is dummy for the moment *)
      let ty = Conv.cty_of_ty (Typing.ty_lval pd loc x) in
      Copn(xs, t, Sopn.Opseudo_op(Pseudo_operator.Oswap ty), es)  
    | Sopn.Oslh (SLHprotect_ptr _), [Lvar x] ->
      (* Fix the size it is dummy for the moment *)
      let xn = size_of (L.unloc x).v_ty in
      let op = Slh_ops.SLHprotect_ptr (Conv.pos_of_int xn) in
      Copn(xs,t, Sopn.Oslh op, es)
    | (Sopn.Opseudo_op(Pseudo_operator.Ocopy _) | Sopn.Oslh (SLHprotect_ptr _)), _ -> assert false
    | _ -> ir
    end

  | Csyscall(xs, o, es) ->
    begin match o with
    | Syscall_t.RandomBytes _ ->
      (* Fix the size it is dummy for the moment *)
      let ty =
        match xs with
        | [x] -> Typing.ty_lval pd loc x
        | _ -> assert false in
      let p = Conv.pos_of_int (Prog.size_of ty) in
      Csyscall(xs, Syscall_t.RandomBytes p, es)
    end

  | Ccall _ -> ir

let iac_func pd f =
  { f with f_body = iac_stmt pd f.f_body }

let doit pd (p:(unit, 'asm) Prog.prog) = (fst p, List.map (iac_func pd) (snd p))

