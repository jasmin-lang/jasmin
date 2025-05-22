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

let size_of_lval =
  function
  | Lvar x -> size_of (L.unloc x).v_ty
  | Lasub (_, ws, len, _, _) -> arr_size ws len
  | Lnone _ | Lmem _ | Laset _ -> assert false


let rec fix_length_e e =
  match e with
  | Pconst _ | Pbool _ | Pvar _ | Parr_init _ | Pis_var_init _ -> e
  | Papp1 (o, e) ->
    let e = fix_length_e e in
    Papp1 (o, e)
  | Papp2 (o, e1, e2) ->
    let e1 = fix_length_e e1 in
    let e2 = fix_length_e e2 in
    Papp2(o, e1, e2)
  | PappN (o, es) ->
    let es = List.map fix_length_e es in
    begin match o, es with

    | O.Ois_arr_init _, e::_ ->
      let ty = Typing.type_of_expr e in
      let len = size_of ty in
      PappN (O.Ois_arr_init (Conv.pos_of_int len), es)
    | Ois_arr_init _, _ -> assert false

    | Ois_barr_init _,  e::_ ->
      let ty = Typing.type_of_expr e in
      let len = size_of ty in
      PappN (O.Ois_barr_init (Conv.pos_of_int len), es)
    | Ois_barr_init _, _ -> assert false

    | Opack _, _ | Ocombine_flags _, _ -> PappN (o, es)
    end
  | Pget (al, aa, ws, x, e) -> Pget (al, aa, ws, x, fix_length_e e)
  | Psub (aa, ws, len, x, e) -> Psub (aa, ws, len, x, fix_length_e e)
  | Pload (al, ws, e) -> Pload (al, ws, fix_length_e e)
  | Pif (ty, e, e1, e2) -> Pif (ty, fix_length_e e, fix_length_e e1, fix_length_e e2)
  | Pbig(e1, op, x, e2, e3, e4) -> Pbig(fix_length_e e1, op, x, fix_length_e e2, fix_length_e e3, fix_length_e e4)
  | Pis_mem_init(e1, e2) -> Pis_mem_init(fix_length_e e1, fix_length_e e2)

let fix_length_es = List.map fix_length_e

let fix_length_lv lv =
 match lv with
 | Lnone _ | Lvar _ -> lv
 | Lmem(al, ws, l, e) ->  Lmem(al, ws, l, fix_length_e e)
 | Laset(al, aa, ws, x, e) -> Laset(al, aa, ws, x, fix_length_e e)
 | Lasub(aa, ws, len, x, e) -> Lasub(aa, ws, len, x, fix_length_e e)

let fix_length_lvs = List.map fix_length_lv

let fix_length_assert (s,e) =  (s,fix_length_e e)

let rec iac_stmt pd is = List.map (iac_instr pd) is
and iac_instr pd i = { i with i_desc = iac_instr_r pd i.i_loc i.i_desc }
and iac_instr_r pd loc ir =
  match ir with
  | Cassgn (x, t, _, e) ->
    let x, e = fix_length_lv x, fix_length_e e in
    if !Glob_options.introduce_array_copy then
      match is_array_copy x e with
      | None -> ir
      | Some (ws, n) ->
         Typing.check_length loc n;
          warning IntroduceArrayCopy
            loc "an array copy is introduced";
          let op = Pseudo_operator.Ocopy(ws, Conv.pos_of_int n) in
          Copn([x], t, Sopn.Opseudo_op op, [e])
    else ir
  | Cif (b, th, el) -> Cif (fix_length_e b, iac_stmt pd th, iac_stmt pd el)
  | Cfor (i, (d, e1, e2), s) ->
    let e1, e2 = fix_length_e e1, fix_length_e e2 in
    Cfor (i, (d, e1, e2), iac_stmt pd s)
  | Cwhile (a, c1, t, info, c2) ->
    Cwhile (a, iac_stmt pd c1, fix_length_e t, info, iac_stmt pd c2)
  | Copn (xs,t,o,es) ->
    let xs, es = fix_length_lvs xs, fix_length_es es in
    begin match o, xs with
    | Sopn.Opseudo_op(Pseudo_operator.Ospill(o,_)), _ ->
      let tys = List.map (fun e -> Conv.cty_of_ty (Typing.ty_expr pd loc e)) es in
      Copn(xs,t, Sopn.Opseudo_op(Pseudo_operator.Ospill(o, tys)), es)

    | Sopn.Opseudo_op(Pseudo_operator.Ocopy(ws, _)), [x] ->
      (* Fix the size it is dummy for the moment *)
      let xn = size_of_lval x in
      let wsn = size_of_ws ws in
      if xn mod wsn <> 0 then
        Typing.error loc
          "the destination %a has size %i: it should be a multiple of %i"
          (Printer.pp_lval ~debug:false) x
          xn wsn
      else
        let len = xn / wsn in
        Typing.check_length loc len;
        let op = Pseudo_operator.Ocopy (ws, Conv.pos_of_int len) in
        Copn(xs,t,Sopn.Opseudo_op op, es)
    | Sopn.Opseudo_op(Pseudo_operator.Oswap _), x::_ ->
      (* Fix the type it is dummy for the moment *)
      let ty = Conv.cty_of_ty (Typing.ty_lval pd loc x) in
      Copn(xs, t, Sopn.Opseudo_op(Pseudo_operator.Oswap ty), es)
    | Sopn.Oslh (SLHprotect_ptr _), [Lvar x] ->
      (* Fix the size it is dummy for the moment *)
      let ws, len = array_kind (L.unloc x).v_ty in
      Typing.check_length loc len;
      let op = Slh_ops.SLHprotect_ptr (ws, Conv.pos_of_int len) in
      Copn(xs,t, Sopn.Oslh op, es)
    | (Sopn.Opseudo_op(Pseudo_operator.Ocopy _) | Sopn.Oslh (SLHprotect_ptr _)), _ -> assert false
    | _ -> ir
    end

  | Csyscall(xs, o, es) ->
    let xs, es = fix_length_lvs xs, fix_length_es es in
    begin match o with
    | Syscall_t.RandomBytes _ ->
      (* Fix the size it is dummy for the moment *)
      let ty =
        match xs with
        | [x] -> Typing.ty_lval pd loc x
        | _ -> assert false in
      let ws, len = array_kind ty in
      Csyscall(xs, Syscall_t.RandomBytes (ws, Conv.pos_of_int len), es)
    end

  | Ccall (xs, f, es) ->
    let xs, es = fix_length_lvs xs, fix_length_es es in
    Ccall(xs, f, es)

  | Cassert (s,e) -> Cassert(s,fix_length_e e)

let fix_length_contra fc =
  { fc with
    f_pre = List.map fix_length_assert fc.f_pre;
    f_post = List.map fix_length_assert fc.f_post
  }

let iac_func pd f =
  { f with
    f_body = iac_stmt pd f.f_body;
    f_contra = Option.map fix_length_contra f.f_contra
  }

let doit pd (p:(unit, 'asm) Prog.prog) : (unit, 'asm) Prog.prog =
  (fst p, List.map (iac_func pd) (snd p))

