open Core_kernel.Std
open IL_Conv
open IL_Lang
open IL_Utils
open IL_Pprint
open Util

let () =
  (* Base type conversions *)
  let s1 = "abcde.777" in
  let s2 = string_of_string0 (string0_of_string s1) in
  assert (s1 = s2);

  (* Types *)
  let check t =
    assert (equal_ty (ty_of_cty (cty_of_ty t)) t)
  in
  check tbool;
  check tu64;
  let at = Arr(U(64),Pconst(Big_int.big_int_of_int 10)) in
  check at;

  (* Variables *)
  let check s n t st =
    let s = Vname.mk s in
    let dloc = Lex.dummy_loc in
    let uloc = Lex.dummy_loc in
    let v1 =
      { Var.name = s;
        Var.num  = n;
        Var.ty   = t;
        Var.stor = st;
        Var.uloc = uloc;
        Var.dloc = dloc;
      }
    in
    let v2 = var_of_cvar (cvar_of_var v1) (s,st,uloc,dloc) in
    if not (Var.equal v1 v2) then
      failwith_ "check variable roundtrip ``%a'' <> ``%a''"
        (pp_var ~pp_types:true) v1
        (pp_var ~pp_types:true) v2
  in
  check "xxxxx" 99 at Reg;
  check "xxxxxaaas" 42 tbool Inline;

  (* pexpr *)
  let check pe1 =
    let cvi = CVI.mk (Fname.Table.create ()) in
    let pe2 = pexpr_of_cpexpr cvi (cpexpr_of_pexpr cvi pe1) in
    if not (equal_pexpr pe1 pe2) then
      failwith_ "check variable roundtrip ``%a'' <> ``%a''"
        (pp_pexpr ~pp_types:true) pe1
        (pp_pexpr ~pp_types:true) pe2
  in
  let pc999 = Pconst(Big_int.big_int_of_int 999) in
  let v1 = 
    { Var.name = Vname.mk "arg0";
      Var.num  = 1;
      Var.ty   = tbool;
      Var.stor = Inline;
      Var.uloc = Lex.dummy_loc;
      Var.dloc = Lex.dummy_loc;
    }
  in
  let pv1 = Patom(Pvar(v1)) in
  let v2 =
    { Var.name = Vname.mk "arg2";
      Var.num  = 2;
      Var.ty   = tu64;
      Var.stor = Reg;
      Var.uloc = Lex.dummy_loc;
      Var.dloc = Lex.dummy_loc;
    }
  in
  let pv2 =  Patom(Pvar(v2)) in
  let v3 =
    { Var.name = Vname.mk "arg2";
      Var.num  = 2;
      Var.ty   = Arr(U(64),Pconst(Big_int.big_int_of_int 10));
      Var.stor = Reg;
      Var.uloc = Lex.dummy_loc;
      Var.dloc = Lex.dummy_loc;
    }
  in
  let pv3 = Patom(Pvar(v3)) in
  let pe1 = Pbinop(Pplus,Pbinop(Pmult,pc999,pv1),Pbinop(Pminus,pc999,pv2)) in
  check pe1;
  let pe2 = Pbinop(Pplus,Pbinop(Pmult,pv2,pv3),Pbinop(Pplus,pc999,pv1)) in
  check pe2;

  (* pcond *)
  let check pc1 =
    let cvi = CVI.mk (Fname.Table.create ()) in
    let pc2 = pcond_of_cpexpr cvi (cpexpr_of_pcond cvi pc1) in
    if not (equal_pcond pc1 pc2) then (
      F.printf "check variable roundtrip@\n``%a''@\n<>@\n``%a''@\n%!"
        (pp_pcond ~pp_types:true) pc1
        (pp_pcond ~pp_types:true) pc2;
      failwith "test failed, see above"
    )
  in
  let pc1 = Pnot(Pbop(Pand,Pbool(true),Pbop(Pand,Pbool(false),Pcmp(Peq,pe1,pe2)))) in
  check pc1;

  (* destinations *)
  let check d1 =
    let cvi = CVI.mk (Fname.Table.create ()) in
    let d2 = dest_of_rval cvi (rval_of_dest cvi d1) in
    if not (equal_dest d1 d2) then (
      F.printf "check variable roundtrip@\n``%a''@\n<>@\n``%a''@\n%!"
        (pp_dest ~pp_types:true) d1
        (pp_dest ~pp_types:true) d2;
      failwith "test failed, see above"
    )
  in
  let sd1 = { d_var = v1; d_idx=None; d_loc = Lex.dummy_loc; } in
  let rd1 = Sdest(sd1) in
  let d1 = Rdest(rd1) in
  check d1;
  let sd2 = { d_var = v3; d_idx=Some(Ivar(v2)); d_loc = Lex.dummy_loc; } in
  let rd2 = Sdest sd2 in
  let d2 = Rdest(rd2) in
  check d2;
  let d3 = Rdest(Mem(sd1, Pconst(Big_int.zero_big_int))) in
  check d3;
  

  (* sources *)
  let check s1 =
    let cvi = CVI.mk (Fname.Table.create ()) in
    let s2 = src_of_cpexpr cvi (cpexpr_of_src cvi s1) in
    if not (equal_src s1 s2) then (
      F.printf "check variable roundtrip@\n``%a''@\n<>@\n``%a''@\n%!"
        (pp_src ~pp_types:true) s1
        (pp_src ~pp_types:true) s2;
      failwith "test failed, see above"
    )
  in
  let s1 = Imm(64,pe1) in
  check s1;
  let s2 = Src(rd1) in
  check s2;
  let s3 = Src(rd2) in
  check s3;
  
  (* base instructions *)
  (* instructions *)
  (* functions *)
  ()
