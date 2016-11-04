(* * Compilation and source-to-source transformations on IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Util
open Arith
open IL_Lang
open IL_Utils
open IL_Pprint
open IL_Map
open IL_Iter

module X64 = Asm_X64
module MP  = MParser
module HT  = Hashtbl
module IS  = Int.Set
(* module IT  = IL_Typing *)


(* ** Simple transformations
 * ------------------------------------------------------------------------ *)

(* ** Register liveness
 * ------------------------------------------------------------------------ *)
(* *** Summary
We follow the terminology and description given in:
  Keith D. Cooper & Linda Torczon - Engineering a compiler
*)
(* *** Code *)

module LV = struct
  type li = {
    var_ue   : IS.t;
    var_kill : IS.t;
    live_out : IS.t;
  }

  (* an instruction can represent leave and enter nodes and we
     want to attach info to both of them *)
  type t = {
    enter : li; 
    leave : li;
  }

  let mk_li () = {
    var_ue   = IS.empty;
    var_kill = IS.empty;
    live_out = IS.empty;
  }

  let mk () = { enter = mk_li (); leave = mk_li () }

  let pp fmt i =
    F.fprintf fmt "lv: \n//    ue=%a\n//    kill=%a\n//    out=%a"
      pp_set_int i.var_ue
      pp_set_int i.var_kill
      pp_set_int i.live_out

end

let compute_kill_ue_block bis =
  let kill = ref IS.empty in
  let ue   = ref IS.empty in
  let handle_var_use v =
    let n = v.Var.num in
    if not (Set.mem !kill n) then
      ue := Set.add !ue n
  in
  let handle_dest d =
    if d.d_idx<>None then (
      F.printf "warning: new_var does not handle %a correctly\n" pp_dest_nt d
    ) else (
      let n = d.d_var.Var.num in
      kill := Set.add !kill n
    )
  in
  let go lbi =
    match lbi.L.l_val with
    | Comment(_) -> ()

    | Assgn(d,s,_) ->
      iter_vars_src ~fvar:handle_var_use s;
      handle_dest d

    | Op(_,ds,ss) ->
      List.iter ~f:(iter_vars_src ~fvar:handle_var_use) ss;
      List.iter ~f:handle_dest ds

    | Load(d,s,pe)    ->
      iter_vars_src ~fvar:handle_var_use s;
      iter_vars_pexpr ~fvar:handle_var_use pe;
      handle_dest d
      
    | Store(s1,pe,s2) ->
      iter_vars_src ~fvar:handle_var_use s1;
      iter_vars_src ~fvar:handle_var_use s2;
      iter_vars_pexpr ~fvar:handle_var_use pe;
      
    | Call(_,_ds,_ss)  -> failwith "call"
  in
  List.iter ~f:go bis;
  { LV.leave =
      { LV.live_out = IS.empty;
        LV.var_ue   = !ue;
        LV.var_kill = !kill };
    LV.enter = LV.mk_li () }

let rec add_kill_ue_instr linstr =
  let instr = linstr.L.l_val in
  let empty_li = LV.mk_li () in
  let instr =
    match instr with
    | Block(bis,_) -> Block(bis,Some(compute_kill_ue_block bis))

    | If(Fcond(fc),s1,s2,_) ->
      let s1 = add_kill_ue_stmt s1 in
      let s2 = add_kill_ue_stmt s2 in
      let i = { LV.leave = empty_li;
                LV.enter = { empty_li
                             with LV.var_ue = IS.singleton fc.fc_var.Var.num }}
      in
      If(Fcond(fc),s1,s2,Some(i))
      
    | While(DoWhile,fc,s,_) ->
      let s = add_kill_ue_stmt s in
      let i = { LV.enter = empty_li;
                LV.leave = { empty_li
                             with LV.var_ue = IS.singleton fc.fc_var.Var.num }}
      in
      While(DoWhile,fc,s,Some(i))
      
    | While(WhileDo,_,_,_)
    | If(Pcond(_),_,_,_)
    | For(_,_,_,_,_)       -> failwith "add liveness annotation: unexpected instruction"
  in
  { linstr with L.l_val = instr }


and add_kill_ue_stmt stmt =
  List.map stmt ~f:add_kill_ue_instr

let update_liveness_stmt stmt _changed lout =
  let _lin info =
    Set.union (Set.diff info.LV.live_out info.LV.var_kill) info.LV.var_ue
  in
  let rec handle li lout =
    let i =
      match li.L.l_val with
      | Block(bis,Some(i))    ->
        Block(bis,Some({ i with LV.leave = {i.LV.leave with LV.live_out = lout }}))
        
      | If(Fcond(fc),s1,s2,i) ->
        If(Fcond(fc),go [] (List.rev s1) lout,go [] (List.rev s2) lout,i)
        
      | While(DoWhile,fc,s,i) ->
        While(DoWhile,fc,go [] (List.rev s) lout,i)
  
      | Block(_,None)
      | If(_,_,_,None)
      | While(_,_,_,None) -> assert false
        
      | While(WhileDo,_,_,_)
      | If(Pcond(_),_,_,_)
      | For(_,_,_,_,_)        -> failwith "update liveness annotation: unexpected instruction"
    in
    { li with L.l_val = i }

  and go acc linstrs lout =
    match linstrs with
    | []      -> acc
    | li::lis -> go ((handle li lout)::acc) lis lout
  in
  go [] (List.rev stmt) lout

let add_liveness_fundef fd =
  let changed = ref false in
  let stmt = ref (add_kill_ue_stmt fd.f_body) in
  let cont = ref false in
  F.printf "   iterate liveness: .%!";
  let lout = IS.of_list (List.map ~f:(fun v -> v.Var.num) fd.f_ret) in
  while !cont do 
    stmt := update_liveness_stmt !stmt changed lout;
    cont := false;
    if not !changed then (
      cont := false
    ) else (
      changed := false;
      F.printf ".%!"
    );
  done;
  F.printf "\n%!";
  { f_call_conv = fd.f_call_conv;
    f_arg       = fd.f_arg;
    f_ret       = fd.f_ret;
    f_body      = !stmt; }

let add_liveness_func func =
  match func with
  | Foreign(_) -> assert false
  | Native(fd) -> Native(add_liveness_fundef fd)

let add_liveness_named_func nf =
  { nf_name = nf.nf_name;
    nf_func = add_liveness_func nf.nf_func; }

let add_liveness_modul modul fname =
  no_nempty_branches_modul modul fname;
  map_named_func modul fname ~f:add_liveness_named_func

(* ** Local SSA *)
(* *** Summary *)
(* *** Code *)

(* **** Maintain renaming info *)

module RNI = struct
  type t = {
    max_num : int ref;
    map     : int       Int.Table.t; (* no entry = never defined *)
    changed : Int.Set.t Int.Table.t; (* indexes for initial vars *)
  }

  let mk max_num = {
    max_num = ref max_num;
    map     = Int.Table.create ();
    changed = Int.Table.create ();
  }

  let rn_var rni v =
    match HT.find rni.map v.Var.num with
    | None    -> failloc_ v.Var.uloc "variable used before definition"
    | Some(n) -> { v with Var.num = n }

  let rn_dest_var rni v =
    let n = !(rni.max_num) in
    incr rni.max_num;
    HT.set rni.map ~key:v.Var.num ~data:n;
    { v with Var.num = n }
  
  let rn_dest rni d =
    if d.d_idx<>None then (
      F.printf "warning: new_var does not handle %a correctly" pp_dest_nt d;
      d
    ) else (
      { d with d_var = rn_dest_var rni d.d_var }
    )

  (*
  let map_get rn_info name =
    HT.find rn_info name |> Option.value ~default:0

  let changed_add rn_info name idx =
    HT.change rn_info.changed name
      ~f:(function | None    -> Some(Int.Set.singleton idx)
                   | Some is -> Some(Set.add is idx))

  let changed_remove rn_info name idx =
    HT.change rn_info.changed name
      ~f:(function | None    -> assert false
                   | Some is -> Some(Set.remove is idx))

  let map_modify rn_info name =
    let max_idx = HT.find rn_info.unused name |> Option.value ~default:1 in
    HT.set rn_info.map    ~key:name ~data:max_idx;
    HT.set rn_info.unused ~key:name ~data:(succ max_idx);
    changed_add rn_info name max_idx

  let mk_reg_name name idx =
    fsprintf "%s_%i" name idx

  let rename rn_info v =
    let num = map_get rn_info.map v.Var.num in
    { v with Var.num = num }
  *)
end

(* **** Synchronize renaming for do-while *)

let rn_map_dowhile_update ~old:_rn_map_enter _rn_info =
  undefined () (*
  let mapping = String.Table.create () in
  let correct = ref [] in
  let handle_changed ~key:name ~data:new_idx =
    let old_idx = RNI.map_get rn_map_enter name in
    if old_idx<>new_idx then (
      let old_name = RNI.mk_reg_name name old_idx in
      let new_name = RNI.mk_reg_name name new_idx in
      (* F.printf "rename  %s to %s\n"  new_name old_name; *)
      HT.add_exn mapping ~key:new_name ~data:old_name;
      RNI.changed_remove rn_info name new_idx;
      correct := (name,old_idx)::!correct
    )
  in
  HT.iteri rn_info.RNI.map ~f:handle_changed;
  List.iter !correct ~f:(fun (s,idx) -> HT.set rn_info.RNI.map ~key:s ~data:idx);
  mapping
               *)

(* **** Synchronize renaming for if *)

let rn_map_if_update _rn_info ~rn_if:_ ~rn_else:_ =
  undefined () (*
  let changed_if   = String.Table.create () in
  let changed_else = String.Table.create () in
  (* populate given maps with changes *)
  let handle_changed _s changed ~key:name ~data:new_idx =
    let old_idx = RNI.map_get rn_info.RNI.map name in
    if old_idx<>new_idx then (
      (* F.printf "changed %s: '%s' from %i to %i\n" s name old_idx new_idx; *)
      HT.set changed ~key:name ~data:();
    ) else (
      (* F.printf "unchanged %s: '%s'\n" s name;  *)
    )
  in
  HT.iteri rn_if   ~f:(handle_changed "if"   changed_if);
  HT.iteri rn_else ~f:(handle_changed "else" changed_else);
  let changed =
    SS.union
      (SS.of_list @@ HT.keys changed_if)
      (SS.of_list @@ HT.keys changed_else)
  in
  (* from new name to old name *)
  let mapping_if_names   = String.Table.create () in
  let mapping_else_names = String.Table.create () in
  (* make renamings consistent for defs that are active when leaving the two branches
     NOTE: we could make this more precise by restricting this to live defs *)
  let merge name =
    (* if a given name has been changed in both, then we choose the higher index *)
    match HT.mem changed_if name, HT.mem changed_else name with
    | false, false -> assert false
    (* defs for name in both, choose larger index from else *)
    | true, true ->
      let idx_if   = RNI.map_get rn_if   name in
      let idx_else = RNI.map_get rn_else name in
      assert (idx_else > idx_if);
      let name_if   = RNI.mk_reg_name name idx_if   in
      let name_else = RNI.mk_reg_name name idx_else in
      (* F.printf "rename %s to %s in if (use else name)\n" name_if name_else; *)
      HT.set mapping_if_names ~key:name_if ~data:name_else;
      (* update rn_map for statements following if-then-else *)
      HT.set rn_info.RNI.map ~key:name ~data:idx_else;
      RNI.changed_remove rn_info name idx_if
    (* def only in if-branch, rename if-def with old name *)
    | true, false ->
      let idx_if    = RNI.map_get rn_if          name in
      let idx_enter = RNI.map_get rn_info.RNI.map name in
      assert (idx_if<>idx_enter);
      let name_if    = RNI.mk_reg_name name idx_if    in
      let name_enter = RNI.mk_reg_name name idx_enter in
      (* F.printf "rename %s to %s in if (use enter name)\n"  name_if name_enter; *)
      HT.set mapping_if_names ~key:name_if ~data:name_enter;
      RNI.changed_remove rn_info name idx_if
    (* def only in else-branch, rename if-def with old name *)
    | false, true ->
      let idx_else  = RNI.map_get rn_else         name in
      let idx_enter = RNI.map_get rn_info.RNI.map name in
      assert (idx_else<>idx_enter);
      let name_else  = RNI.mk_reg_name name idx_else in
      let name_enter = RNI.mk_reg_name name idx_enter  in
      (* F.printf "rename %s to %s in else (use enter name)\n" name_else name_enter; *)
      HT.set mapping_else_names ~key:name_else ~data:name_enter;
      RNI.changed_remove rn_info name idx_else
  in
  SS.iter changed ~f:merge;
  mapping_if_names, mapping_else_names
*)

(*
RENAME a block:
*)

let local_ssa_base_instr rni lbi =
  let bi = lbi.L.l_val in
  let bi =
    match bi with
    | Comment(_)      -> bi
    | Assgn(d,s,at)   ->
      let s = map_vars_src ~f:(RNI.rn_var rni) s in
      let d = RNI.rn_dest rni d in
      Assgn(d,s,at)
    | Op(o,ds,ss)     ->
      let ss = List.map ~f:(map_vars_src ~f:(RNI.rn_var rni)) ss in
      let ds = List.map ~f:(RNI.rn_dest rni) ds in
      Op(o,ds,ss)
    | Load(_d,_s,_pe)    -> failwith "load"
    | Store(_s1,_pe,_s2) -> failwith "store"
    | Call(_fn,_ds,_ss)  -> failwith "call"
  in
  { lbi with L.l_val = bi }

let rec local_ssa_instr rni linstr =
  (* let _rename = RNI.rename rni in *)
  let instr = linstr.L.l_val in
  let instr =
    match instr with

    | Block(bis,_) ->
      (* rename RHS *)
      (* FIXME: how to treat arr[i] = 5? *)
      (* let bi = rename_base_instr ~rn_type:UseOnly rename bi in *)
      (* update renaming map and rename LHS *)
      (* let def_vars = def_binstr bi in *)
      (* SS.iter def_vars ~f:(fun s -> RNI.map_modify rn_info s); *)
      (* let bi = rename_base_instr ~rn_type:DefOnly rename bi in *)
      let bis = List.map ~f:(local_ssa_base_instr rni) bis in
      Block(bis,None)

    | If(Fcond(fc),s1,s2,_) ->
      let rn_map_if   = HT.copy rni.RNI.map in
      let rn_map_else = HT.copy rni.RNI.map in
      let fc = map_vars_fcond ~f:(RNI.rn_var rni) fc in
      let s1 = local_ssa_stmt { rni with RNI.map=rn_map_if   } s1 in
      let s2 = local_ssa_stmt { rni with RNI.map=rn_map_else } s2 in
      
      If(Fcond(fc),local_ssa_stmt rni s1,local_ssa_stmt rni s2, None)
      (*
      let rn_sync_if, rn_sync_else =
        rn_map_if_update rn_info ~rn_if:rn_map_if ~rn_else:rn_map_else
      in
      let rn rns s = HT.find rns s |> Option.value ~default:s in
      let s1 = rename_stmt (rn rn_sync_if)   s1 in
      let s2 = rename_stmt (rn rn_sync_else) s2 in
      If(Fcond(fc),s1,s2)
      *)
      
    | While(DoWhile,_fc,_s,_) -> instr
      (*
      let rn_map_enter = HT.copy rn_info.RNI.map in
      let s = local_ssa_stmt rn_info s in
      (* rename fc with the rn_map for leave *)
      let fc = rename_fcond rename fc in
      (* make last def-index coincide with def-index from entering *)
      let rn_sync = rn_map_dowhile_update ~old:rn_map_enter rn_info in
      let rn s = HT.find rn_sync s |> Option.value ~default:s in
      let fc = rename_fcond rn fc in
      let s  = rename_stmt rn s in
      While(DoWhile,fc,s)
      *)
      
    | While(WhileDo,_fc,_s,_) ->
      failwith "INCOMPLETE"

    | If(Pcond(_),_,_,_)
    | For(_,_,_,_,_)     -> failwith "local SSA transformation: unexpected instruction"
  in
  { linstr with L.l_val = instr }

and local_ssa_stmt rni stmt =
  List.map ~f:(local_ssa_instr rni) stmt

let local_ssa_fundef fd =
  let mn = max_var_fundef fd in
  let rni = RNI.mk mn in
  let arg = List.map ~f:(RNI.rn_dest_var rni) fd.f_arg in
  let body = local_ssa_stmt rni fd.f_body in
  let ret = List.map ~f:(RNI.rn_var rni) fd.f_ret in
  { fd with
    f_body = body; f_ret = ret; f_arg = arg}

let local_ssa_func func =
  match func with
  | Foreign(fo) -> Foreign(fo)
  | Native(fd)  -> Native(local_ssa_fundef fd)

let local_ssa_modul modul fname =
  map_func modul fname ~f:local_ssa_func
 
(* ** Collect equality and fixed register constraints from +=, -=, :=, ...
 * ------------------------------------------------------------------------ *)
(*
module REGI = struct
  type t = {
    class_of : string String.Table.t;
    rank_of  : int    String.Table.t;
    fixed    : int    String.Table.t;
  }

  let mk () = {
    class_of = String.Table.create ();
    rank_of  = String.Table.create ();
    fixed    = String.Table.create ();
  }

  let rec class_of rinfo name =
    match HT.find rinfo.class_of name with
    | None -> name
    | Some(p_name) ->
      let e_name = class_of rinfo p_name in
      if name<>p_name then HT.set rinfo.class_of ~key:name ~data:e_name;
      e_name

  let get_classes rinfo =
    let classes = String.Table.create () in
    let keys = HT.keys rinfo.class_of in
    List.iter keys
      ~f:(fun n ->
            let r = class_of rinfo n in 
            HT.change classes r
              ~f:(map_opt_def ~d:(SS.singleton n)
                              ~f:(fun ss -> SS.add ss n)));
    classes

  let rank_of rinfo name =
    HT.find rinfo.rank_of name |> get_opt 0

  let fix_class rinfo name reg =
    let s = class_of rinfo name in
    match HT.find rinfo.fixed s with
    | None ->
      HT.set rinfo.fixed ~key:s ~data:reg
    | Some(reg') when reg = reg' -> ()
    | Some(reg') ->
      failwith_  "conflicting requirements: %a vs %a for %s"
        X64.pp_int_reg reg' X64.pp_int_reg reg name

  let union_fixed rinfo ~keep:s1 ~merge:s2 =
    match HT.find rinfo.fixed s2 with
    | Some(r) -> fix_class rinfo s1 r
    | None    -> ()

  let union_class rinfo d1 d2 =
    failwith "undefined"
    (*
    let root1 = class_of rinfo d1.d_name in
    let root2 = class_of rinfo d2.d_name in
    if root1<>root2 then (
      let rank1 = rank_of rinfo root1 in
      let rank2 = rank_of rinfo root2 in
      match () with
      | _ when rank1 < rank2 ->
        HT.set rinfo.class_of ~key:root1 ~data:root2;
        union_fixed rinfo ~keep:root2 ~merge:root1
      | _ when rank2 < rank1 ->
        HT.set rinfo.class_of ~key:root2 ~data:root1;
        union_fixed rinfo ~keep:root1 ~merge:root2
      | _ ->
        HT.set rinfo.class_of ~key:root1 ~data:root2;
        union_fixed rinfo ~keep:root2 ~merge:root1;
        HT.set rinfo.rank_of  ~key:root2 ~data:(rank2 + 1)
    )
    *)

  let pp_fixed fmt (i,_l) = X64.pp_int_reg fmt i

  let pp fmt rinfo =
    F.fprintf fmt
      ("classes: %a\n"^^"ri_fixed: %a\n")
      (pp_ht ", "  "->" pp_string pp_set_string)  (get_classes rinfo)
      (pp_ht ", "  "->" pp_string X64.pp_int_reg) rinfo.fixed

end

let reg_info_binstr rinfo bi =
    failwith "undefined"
    (*
  let is_reg_dest d =
    let (t,s) = d.d_decl in
    if s = Reg
    then ( assert (t = U64 && d.d_idx=inone); true )
    else ( false )
  in
  let is_reg_src s =
    match s with
    | Imm(_) -> assert false
    | Src(d) -> is_reg_dest d
  in
  let reg_info_op op ds ss =
    match view_op op ds ss with

    | V_Umul(d1,d2,s1,_)
      when is_reg_dest d1 && is_reg_dest d2 && is_reg_src s1 ->
      REGI.union_class rinfo (get_src_dest_exn s1) d2;
      REGI.fix_class rinfo d2.d_name (X64.int_of_reg X64.RAX);
      REGI.fix_class rinfo d1.d_name (X64.int_of_reg X64.RDX)
        

    | V_Carry(_,_,d2,s1,_,_)
      when is_reg_dest d2 && is_reg_src s1 ->
      REGI.union_class rinfo (get_src_dest_exn s1) d2

    | V_ThreeOp(_,d1,s1,_)
    | V_Cmov(_,d1,s1,_,_)
    | V_Shift(_,_,d1,s1,_) when is_reg_dest d1 && is_reg_src s1 ->
      REGI.union_class rinfo (get_src_dest_exn s1) d1

    | V_ThreeOp(O_Imul,_,_,Imm(_))-> ()

    | V_Umul(d1,_,_,_)      -> failtype_ d1.d_loc "reg-alloc"
    | V_ThreeOp(_,d1,_,_)   -> failtype_ d1.d_loc "reg-alloc"
    | V_Carry(_,_,d1,_,_,_) -> failtype_ d1.d_loc "reg-alloc"
    | V_Cmov(_,d1,_,_,_)    -> failtype_ d1.d_loc "reg-alloc"
    | V_Shift(_,_,d1,_,_)   -> failtype_ d1.d_loc "reg-alloc"
  in
  match bi with

  | Op(o,ds,ss) ->
    reg_info_op o ds ss

  (* FIXME: do the same for arrays, stack variables *)
  | Assgn(d,s,Eq) when is_reg_dest d ->
    begin match s with
    | Imm(_) -> assert false
    | Src(s) -> ignore(REGI.union_class rinfo s d)
    end

  | Load(_,_,_)
  | Assgn(_,_,_)
  | Store(_,_,_)
  | Comment(_)   -> ()

  | Call(_) -> failwith "inline calls before register allocation"
    *)

let rec reg_info_instr rinfo li =
  failwith "undefined"
(*
  let ri_stmt = reg_info_stmt rinfo in
  let ri_binstr = reg_info_binstr rinfo in
  match li.i_val with
  | Block(bis,_)       -> failwith "undefined" (* ri_binstr bi *)
  | While(_,_fc,s)     -> ri_stmt s
  | If(Fcond(_),s1,s2) -> ri_stmt s1; ri_stmt s2

  | If(Pcond(_),_,_)
  | For(_,_,_,_)     -> failwith "register allocation: unexpected instruction"
*)

and reg_info_stmt rinfo stmt =
  List.iter ~f:(reg_info_instr rinfo) stmt

let reg_info_func rinfo func fdef =
  failwith "undefined"
(*
  let fix_regs_args rinfo =
    let arg_len  = List.length func.f_args in
    let arg_regs = List.take X64.arg_regs arg_len in
    if List.length arg_regs < arg_len then (
      let arg_max  = List.length X64.arg_regs in
      failwith_ "register_alloc: at most %i arguments supported" arg_max
    );
    List.iter (List.zip_exn func.f_args arg_regs)
      ~f:(fun ((s,n,t),arg_reg) ->
            assert (s = Reg && t = U64);
            REGI.fix_class rinfo n (X64.int_of_reg arg_reg))
  in
  let fix_regs_ret rinfo =
    let ret_extern_regs = List.map ~f:X64.int_of_reg X64.[RAX; RDX] in
    let ret_len = List.length fdef.fd_ret in
    let ret_regs = List.take ret_extern_regs ret_len in
    if List.length ret_regs < ret_len then (
      let ret_max = List.length ret_extern_regs in
      failwith_ "register_alloc: at most %i arguments supported" ret_max
    );
    List.iter (List.zip_exn fdef.fd_ret ret_regs)
      ~f:(fun (n,ret_reg) -> REGI.fix_class rinfo n ret_reg)
  in

  fix_regs_args rinfo;
  fix_regs_ret rinfo;
  reg_info_stmt rinfo fdef.fd_body
  (* F.printf "\n%a\n%!" REGI.pp rinfo *)
*)

(* ** Register allocation
 * ------------------------------------------------------------------------ *)

(* lower registers are special purpose, so we take the maximum free one *)
let max_not_in reg_num rs =
  let module E = struct exception Found of unit end in
  let ri = ref (reg_num - 1) in
  let lrs = List.rev @@ List.sort ~cmp:compare rs in
  (try (
    List.iter lrs ~f:(fun i -> if i = !ri then decr ri else raise (E.Found()))
   ) with
    E.Found() -> ()
  );
  if !ri >= 0 then (
    !ri
  ) else
    failwith "Cannot find free register"

let assign_reg reg_num denv conflicts classes rinfo cur_pos name =
  let dbg = ref false in
  let watch_list = []
    (* ["bit_3__0";"j_3__0";"swap_3__0";] *)
  in
  match Map.find denv name with
  | Some(U64,Reg) ->
    (* F.printf "assigning register to %s @@ %a\n" n pp_pos cur_pos; *)
    let cl = REGI.class_of rinfo name in
    if List.mem watch_list name || List.mem watch_list cl
    then (
      dbg := true;
      F.printf "Here we are: %s %a\n%!" name pp_pos cur_pos
    );
    let ofixed = HT.find rinfo.REGI.fixed cl in
    if !dbg then F.printf "  in class %s fixed to %a\n%!" cl (pp_opt "-" X64.pp_int_reg) ofixed;
    let class_name = HT.find classes cl |> Option.value ~default:(SS.singleton cl) in
    let conflicted = String.Table.create () in
    SS.iter class_name
      ~f:(fun n ->
            match HT.find conflicts n with
            | None -> ()
            | Some(ht) ->
                HT.iter_keys ht
                  ~f:(fun n ->
                        let (t,s) = Map.find_exn denv n in
                        if s = Reg && t = U64 then HT.set conflicted ~key:n ~data:()));
    if !dbg then F.printf "  conflicted with %a\n%!" (pp_list "," pp_string) (HT.keys conflicted);
    let conflicted_fixed = Int.Table.create () in
    HT.iter_keys conflicted ~f:(fun n ->
                                  match HT.find rinfo.REGI.fixed (REGI.class_of rinfo n) with
                                  | None     -> ()
                                  | Some(ri) -> HT.set conflicted_fixed ~key:ri ~data:());
    if !dbg then
      F.printf "  conflicted with fixed %a\n%!"
        (pp_list "," X64.pp_int_reg) (HT.keys conflicted_fixed);
    begin match ofixed with
    | None ->
      let ri = max_not_in reg_num (HT.keys conflicted_fixed) in
      REGI.fix_class rinfo cl ri;
      if !dbg then F.printf "  fixed register to %a\n%!" X64.pp_int_reg ri
    | Some(ri) ->
      if HT.mem conflicted_fixed ri then (
        F.printf "\n\nERROR:\n\n%!";
        F.printf "  reg %s in class %s fixed to %a\n%!" name cl (pp_opt "-" X64.pp_int_reg) ofixed;
        F.printf "  conflicted with %a\n%!" (pp_list "," pp_string) (HT.keys conflicted);
        let f n =
          Option.bind (HT.find rinfo.REGI.fixed (REGI.class_of rinfo n))
            (fun i -> if i = ri then Some (n,i) else None)
        in
        let conflicted_fixed = List.filter_map ~f (HT.keys conflicted) in
        F.printf "  conflicted with fixed %a\n%!"
          (pp_list "," (pp_pair ":" pp_string X64.pp_int_reg)) conflicted_fixed;
        
        failwith_ "assign_reg: conflict between fixed registers"
      )
    end

  | None -> assert false

  | Some(_t,_s) -> ()

let assign_regs _reg_num _denv (_conflicts : (unit String.Table.t) String.Table.t) _linfo _rinfo =
  failwith "undefined"
(*
  let visited = Pos.Table.create () in
  let visit   = ref [LI.enter_fun_pos] in
  let classes = REGI.get_classes rinfo in

  while !visit<>[] do
    let cur_pos,rem_pos = match !visit with p::ps -> (p,ps) | [] -> assert false in
    visit := rem_pos;
    if not (HT.mem visited cur_pos) then (
      HT.set visited ~key:cur_pos ~data:();
      (* get defined variables *)
      let defs = SS.to_list @@ LI.get_def linfo cur_pos in
      List.iter defs ~f:(assign_reg reg_num denv conflicts classes rinfo cur_pos);
      visit := !visit @ (Set.to_list @@ LI.get_succ linfo cur_pos)
    )
  done
*)

let reg_alloc_func _reg_num func =
  undefined ()
(*
  assert (func.f_call_conv = Extern);
  let rename denv rinfo name =
    match Map.find denv name with
    | None -> assert false
    | Some(U64,Reg) ->
      let cl = REGI.class_of rinfo name in
      let ri = HT.find_exn rinfo.REGI.fixed cl in
      fsprintf "r_%i_%a" ri X64.pp_int_reg ri
    | Some(_,_) ->
      name
  in
  let _extract_conflicts _linfo _conflicts ~key:_pos ~data:_live_set =
    failwith "undefined"
    (*
    let defs = LI.get_def linfo pos in
    let add_set (ht : unit String.Table.t) live_set n' =
      SS.iter live_set
        ~f:(fun n -> if n<>n' then HT.set ht ~key:n ~data:());
      ht
    in
    let new_set live_set n =
      add_set (String.Table.create ()) live_set n
    in
    SS.iter (SS.union live_set defs)
      ~f:(fun n ->
            HT.change conflicts n
              ~f:(function | None     -> Some(new_set live_set n)
                           | Some(ht) -> Some(add_set ht live_set n)))
    *)
  in
  let print_time start stop = F.printf "   %fs\n%!" (stop -. start) in

  F.printf "-> computing equality and fixed constraints\n%!";
  let rinfo = REGI.mk () in
  let t1 = Unix.gettimeofday () in
  let fd = get_fundef ~err_s:"perform register allocation" func in
  reg_info_func rinfo func fd;
  let t2 = Unix.gettimeofday () in
  print_time t1 t2;

  F.printf "-> computing liveness\n%!";
  let _linfo = failwith "undefined" (*compute_liveness_func func*) in
  let _conflicts = String.Table.create () in
  let t3 = Unix.gettimeofday () in
  print_time t2 t3;

  F.printf "-> computing conflicts\n%!";
  (* HT.iteri linfo.LI.live_after ~f:(extract_conflicts linfo conflicts); *)
  let denv = IT.denv_of_func func (IT.extract_decls func.f_args fd) in
  let t4 = Unix.gettimeofday () in
  print_time t3 t4;

  F.printf "-> assigning registers\n%!";
  (* assign_regs reg_num denv conflicts linfo rinfo; *)
  let t5 = Unix.gettimeofday () in
  print_time t4 t5;

  F.printf "-> renaming variables\n%!";
  (*
  let func = rename_func (rename denv rinfo) func in
  *)
  let t6 = Unix.gettimeofday () in
  print_time t5 t6;
  func
*)
  
let reg_alloc_modul reg_num modul fname =
  map_fun ~f:(reg_alloc_func reg_num) modul fname

(* ** Remove equality constraints
 * ------------------------------------------------------------------------ *)

let remove_eq_constrs_instr _pos info instr =
  failwith "undefined"
(*
  match instr with
  | Block(Assgn(d1,Src(d2),Eq) as bi) ->
    if (d1.d_name <> d2.d_name) then (
      failtype_ d1.d_loc
        "Removing equality constraints: RHS and LHS not equal in `%a'" pp_base_instr bi
    ) else (
      []
    )
  | Binstr(Assgn(d,Imm(_),Eq) as bi) ->
    failtype_ d.d_loc "Removing equality constraints: RHS cannot be immediate in `%a'"
      pp_base_instr bi
  | _ -> [{ i_val = instr; i_loc = loc; i_info = info}]
*)

let remove_eq_constrs_modul modul fname =
  concat_map_modul modul fname ~f:remove_eq_constrs_instr

(* ** Translation to assembly
 * ------------------------------------------------------------------------ *)

let to_asm_x64 _efun =
  failwith "undefined"
  (*
  let mreg_of_preg pr =
    let fail () =
      failwith
        (fsprintf "to_asm_x64: expected register of the form %%i, got %a" pp_preg_ty pr)
    in
    let s = if pr_is_indexed pr then fail () else pr.pr_name in
    let i =
      try
        begin match String.split s ~on:'%' with
        | ""::[s] -> int_of_string s
        | _       -> fail ()
        end
      with
      | Failure "int_of_string" -> fail ()
    in
    X64.reg_of_int i
  in
  let ensure_dest_mreg d mr msg =
    match d with
    | Dreg(pr) when mreg_of_preg pr = mr -> ()
    | _                                  -> failwith msg
  in
  let ensure_src_mreg s mr msg =
    match s with
    | Sreg(pr) when mreg_of_preg pr = mr -> ()
    | _                                  -> failwith msg
  in
  let ensure c msg = if not c then failwith ("to_asm_x64: "^msg) in
  let trans_cexpr = function
    | Cconst(i) -> i
    | Cvar(_)
    | Cbinop(_) ->
      failwith "to_asm_x64: cannot translate non-constant c-expressions"
  in
  let trans_src = function
    | Sreg(r)    -> X64.Sreg(mreg_of_preg r)
    | Simm(i)    -> X64.Simm(i)
    | Smem(r,ie) -> X64.Smem(mreg_of_preg r,trans_cexpr ie)
  in
  let trans_dest = function
    | Dreg(r)    -> X64.Dreg(mreg_of_preg r)
    | Dmem(r,ie) -> X64.Dmem(mreg_of_preg r,trans_cexpr ie)
  in
  let trans bi =
    let c = X64.Comment (fsprintf "mil: %a" pp_base_instr bi) in
    match bi with

    | Comment(s) ->
      [X64.Comment(s)]

    | App(Assgn,[d],[s]) ->
      [c; X64.( Binop(Mov,trans_src s,trans_dest d) )]

    | App(UMul,[dh;dl],[s1;s2]) ->
      ensure_dest_mreg dh X64.RDX "mulq high result must be %rdx";
      ensure_dest_mreg dl X64.RAX "mulq low result must be %rax";
      ensure_src_mreg  s1 X64.RAX "mulq source 1 must be %rax";

      let instr = X64.( Unop(Mul,trans_src s2) ) in
      [c;instr]

    | App(IMul,[dl],[s1;s2]) ->
      ensure (not (is_src_imm s1))  "imul source 1 cannot be immediate";
      ensure (is_src_imm s2)  "imul source 2 must be immediate";
      ensure (is_dest_reg dl) "imul dest must be register";
      [c; X64.( Triop(IMul,trans_src s2,trans_src s1,trans_dest dl) )]

    | App(Cmov(CfSet(b)),[d],[s1;s2;_cin]) ->
      ensure (equal_src (dest_to_src d) s1) "cmov with dest<>src1";
      let instr = X64.( Binop(Cmov(CfSet(b)),trans_src s2,trans_dest d) ) in
      [c; instr]

    | App(Shift(dir),[d],[s1;s2]) ->
      ensure (equal_src (dest_to_src d) s1) "shift with dest<>src1";
      ensure (is_src_imm s2)  "shift source 2 must be immediate";
      let op = match dir with Right -> X64.Shr | Left -> X64.Shl in
      let instr = X64.( Binop(op,trans_src s2,trans_dest d) )  in
      [c;instr]

    | App(Xor,[d],[s1;s2]) ->
      ensure (equal_src (dest_to_src d) s1) "add/sub with dest<>src1";
      let instr = X64.( Binop(Xor,trans_src s2,trans_dest d) )  in
      [c;instr]

    | App(op,([_;d] | [d]),s1::s2::cin) ->
      ensure (equal_src (dest_to_src d) s1) "add/sub with dest<>src1";
      let instr =
        match op,cin with
        | Add,  []  -> X64.( Binop(Add,trans_src s2,trans_dest d) )
        | Add,  [_] -> X64.( Binop(Adc,trans_src s2,trans_dest d) )
        | BAnd, []  -> X64.( Binop(And,trans_src s2,trans_dest d) )
        | BAnd, [_] -> assert false
        | Sub,  []  -> X64.( Binop(Sub,trans_src s2,trans_dest d) )
        | Sub,  [_] -> X64.( Binop(Sbb,trans_src s2,trans_dest d) )
        | _         -> assert false
      in
      [c; instr]

    | _ -> assert false
  in
  let asm_code =
    List.concat_map ~f:trans (stmt_to_base_instrs efun.ef_body)
  in
  X64.(
    { af_name = efun.ef_name;
      af_body = asm_code;
      af_args = failwith "List.map ~f:mreg_of_preg efun.ef_args";
      af_ret  = failwith "List.map ~f:mreg_of_preg efun.ef_ret";
    }
  )
  *)
*)
(* ** Calling convention for "extern" functions
 * ------------------------------------------------------------------------ *)

let push_pop_call_reg op  =
  let call_reg =
    X64.([ X64.Sreg R11;
           Sreg R12;
           Sreg R13;
           Sreg R14;
           Sreg R15;
           Sreg RBX;
           Sreg RBP
         ])
  in
  List.map ~f:(fun reg -> X64.Unop(op,reg)) call_reg

let wrap_asm_function afun =
  let name = "_"^afun.X64.af_name in
  let prefix =
    X64.([ Section "text";
           Global name;
           Label name;
           Binop(Mov,Sreg RSP,Dreg R11);
           Binop(And,Simm (U64.of_int 31),Dreg R11);
           Binop(Sub,Sreg R11,Dreg RSP)
    ]) @ (push_pop_call_reg X64.Push )
  in
  let suffix =
      (List.rev (push_pop_call_reg X64.Pop ))
    @ X64.([ Binop(Add,Sreg R11,Dreg RSP); Ret ])
  in
  prefix @ afun.X64.af_body @ suffix
