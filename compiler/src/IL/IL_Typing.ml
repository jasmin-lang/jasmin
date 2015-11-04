(* * Typing and well-formedness of IL *)

open IL_Lang
open IL_Utils
open Util
open Core_kernel.Std

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

type fun_env = efun String.Table.t

type type_env = ty String.Table.t

let type_efun (efun : IL_Lang.efun_ut) (fun_env : fun_env) : IL_Lang.efun =
  let ty_env =  String.Table.create () in
  List.iter
    ~f:(fun pr ->
          assert (not (pr_is_indexed pr));
          Hashtbl.set ty_env ~key:pr.pr_name ~data:pr.pr_aux)
    (efun.ef_args @ efun.ef_decls);
  let pr_set_type t pr = { pr with pr_aux = t } in
  let pr_to_string pr = fsprintf "%a" pp_preg pr in
  let assert_equal_ty s ety gty =
    if not (equal_ty ety gty) then
      failwith (fsprintf "wrong type for %s, expected %a, got %a." s pp_ty ety pp_ty gty)
  in
  let type_preg pr =
    let name_ty = Hashtbl.find_exn ty_env pr.pr_name in
    
    let ty =
      match name_ty with
      | Ivals(_ces) when pr_is_range pr ->
        name_ty
      | Ivals(ces) ->
        assert (List.length ces = pr_index_length pr);
        U64
      | Array(_ces) ->
        assert (not (pr_is_indexed pr));
        name_ty
      | (Bool | U64) -> 
        name_ty
    in
    ty, pr_set_type ty pr
  in 
  let type_src ?exp s =
    let assert_type pr t =
      match exp with
      | None    -> ()
      | Some t' -> assert_equal_ty pr t' t
    in
    match s with

    | Simm(i)  ->
      assert_type "immediate" U64;
      U64, Simm(i)

    | Sreg(pr) ->
      let ty, pr = type_preg pr in
      assert_type (fsprintf "%a" pp_preg pr) ty;
      ty, Sreg(pr)

    | Smem(pr,offset) ->
      let name_ty = Hashtbl.find_exn ty_env pr.pr_name in
      let ty =
        match name_ty with
        | Ivals(_ces) -> failwith (fsprintf "got destination %a for array" pp_src s)
        | Array(ces) ->
          assert (List.length ces = List.length [offset]);
          U64
        | (Bool | U64) -> assert false
      in
      assert_type (pr_to_string pr) ty;
      ty, Smem(pr_set_type name_ty pr,offset)
  in
  let type_dst t d =
    match d with

    | Dreg(pr) when not (pr_is_indexed pr) ->
      Hashtbl.set ty_env ~key:pr.pr_name ~data:t;
      Dreg(pr_set_type t pr)

    | Dreg(pr) ->
      let name_ty = Hashtbl.find_exn ty_env pr.pr_name in
      let ty =
        match name_ty with
        | Ivals(_ces) when pr_is_range pr ->
          name_ty
        | Ivals(ces) ->
          assert (List.length ces = pr_index_length pr);
          U64
        | Array(_ces) -> assert false
        | (Bool | U64) -> assert false
      in
      assert_equal_ty (pr_to_string pr) t ty;
      Dreg(pr_set_type t pr)

    | Dmem(pr,offset) ->
      let name_ty = Hashtbl.find_exn ty_env pr.pr_name in
      let ty =
        match name_ty with
        | Ivals(_ces) -> failwith (fsprintf "got destination %a for array" pp_dest d)
        | Array(ces) ->
          assert (List.length ces = List.length [offset]);
          U64
        | (Bool | U64) -> assert false
      in
      assert_equal_ty (pr_to_string pr) t ty;
      Dmem(pr_set_type name_ty pr,offset)
  in
  let type_app = function

    | A_Assgn(d,s) ->
      let s_t, s = type_src s in
      let d      = type_dst s_t d in
      app_view_to_app (A_Assgn(d,s))

    | A_UMul((h,l),(x,y)) ->
      let _, x = type_src ~exp:U64 x in
      let _, y = type_src ~exp:U64 y in
      let h = type_dst U64 h in
      let l = type_dst U64 l in
      app_view_to_app (A_UMul((h,l),(x,y)))

    | A_Carry(cop,(mcf_out,z),(x,y,mcf_in)) ->
      let _,x = type_src ~exp:U64 x in
      let _,y = type_src ~exp:U64 y in
      let mcf_in =  Option.map ~f:(fun s -> snd (type_src ~exp:Bool s)) mcf_in in
      let mcf_out = Option.map ~f:(type_dst Bool) mcf_out in
      let z = type_dst U64 z in
      app_view_to_app (A_Carry(cop,(mcf_out,z),(x,y,mcf_in)))

    | A_CMov(cf,z,(x,y,cf_in))  ->
      let _,x = type_src ~exp:U64 x in
      let _,y = type_src ~exp:U64 y in
      let _,cf_in = type_src ~exp:Bool cf_in in
      let z = type_dst U64 z in
      app_view_to_app (A_CMov(cf,z,(x,y,cf_in)))
      
    | A_IMul(z,(x,y)) ->
      let _,x = type_src ~exp:U64 x in
      let _,y = type_src ~exp:U64 y in
      let z = type_dst U64 z in
      app_view_to_app (A_IMul(z,(x,y)))
    
    | A_Logic(_lop,_d,(_s1,_s2)) ->
      failwith "not implemented"

    | A_Shift(_dir,(_mcf_out,_z),(_x,_cn)) ->
      failwith "not implemented"

  in
  let rec type_instr instr =
    match instr with

    | BInstr(Comment c) -> BInstr(Comment c)

    | BInstr(App(o,dests,srcs)) -> BInstr(type_app (app_view (o,dests,srcs)))

    | If(ccond,stmt1,stmt2) ->
      let stmt1 = stmt_type stmt1 in
      let stmt2 = stmt_type stmt2 in
      If(ccond,stmt1,stmt2)
    
    | For(v,lb,ub,stmt) ->
      let stmt = stmt_type stmt in
      For(v,lb,ub,stmt)

    | Call(fname,ds,args) ->
      let cfun = Hashtbl.find_exn fun_env fname in
      let args =
        List.map2_exn
          ~f:(fun (a : src_ut) (cpr : preg) ->
              match a with
              | Sreg(pr) ->
                Sreg({ pr with pr_aux = cpr.pr_aux })
              | _ -> assert false)
          args cfun.ef_args
      in
      let ds =
        List.map2_exn
          ~f:(fun (a : dest_ut) (cpr : preg) ->
              match a with
              | Dreg(pr) ->
                Dreg({ pr with pr_aux = cpr.pr_aux })
              | _ -> assert false)
          ds cfun.ef_ret
      in
      Call(fname,ds,args)
      
  and stmt_type stmt = List.map ~f:type_instr stmt in
  let ef_ret = List.map ~f:(fun pr -> snd (type_preg pr)) efun.ef_ret in
  let body = stmt_type efun.ef_body in
  { ef_name   = efun.ef_name;
    ef_extern = efun.ef_extern;
    ef_params = efun.ef_params;
    ef_args   = efun.ef_args;
    ef_decls  = efun.ef_decls;
    ef_body   = body;
    ef_ret    = ef_ret
  }

let type_efuns (efuns : IL_Lang.efun_ut list) : IL_Lang.efun list =
  let smap = String.Table.create () in
  List.map efuns
    ~f:(fun ef ->
          let efun = type_efun ef smap in
          Hashtbl.add_exn smap ~key:efun.ef_name ~data:efun;
          efun)
