(* * Compilation and source-to-source transformations on IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Util
open Arith
open IL_Lang
open IL_Utils

module X64 = Asm_X64
module MP  = MParser
module HT  = Hashtbl
module IT  = IL_Typing

(* ** Register liveness
 * ------------------------------------------------------------------------ *)

(* *** Liveness information definitions *)

module LI = struct 
  (* hashtable that holds the CFG and the current liveness information *)
  type t = {
    use         : SS.t      Pos.Table.t;
    def         : SS.t      Pos.Table.t;
    succ        : Pos.Set.t Pos.Table.t;
    pred        : Pos.Set.t Pos.Table.t;
    live_before : SS.t      Pos.Table.t;
    live_after  : SS.t      Pos.Table.t;
    str         : string    Pos.Table.t;
  }

  let mk () =
    { use         = Pos.Table.create ()
    ; def         = Pos.Table.create ()
    ; succ        = Pos.Table.create ()
    ; pred        = Pos.Table.create ()
    ; str         = Pos.Table.create ()
    ; live_before = Pos.Table.create ()
    ; live_after  = Pos.Table.create () }

  let enter_fun_pos  = [-1]
  let return_fun_pos = [-2]

  let get_use linfo pos = hashtbl_find_exn linfo.use pp_pos pos 
  let get_def linfo pos = hashtbl_find_exn linfo.def pp_pos pos
  let get_str linfo pos = hashtbl_find_exn linfo.str pp_pos pos
  let get_pred linfo pos =
    Pos.Table.find linfo.pred pos |> Option.value ~default:Pos.Set.empty
  let get_succ linfo pos =
    Pos.Table.find linfo.succ pos |> Option.value ~default:Pos.Set.empty
  let get_live_before linfo pos =
    Pos.Table.find linfo.live_before pos |> Option.value ~default:SS.empty
  let get_live_after linfo pos =
    Pos.Table.find linfo.live_after pos |> Option.value ~default:SS.empty

  let add_succ linfo ~pos ~succ =
    Pos.Table.change linfo.succ pos
      ~f:(function | None   -> Some(Pos.Set.singleton succ)
                   | Some s -> Some(Pos.Set.add s     succ))

  let add_pred linfo ~pos ~pred =
    Pos.Table.change linfo.pred pos
      ~f:(function | None   -> Some(Pos.Set.singleton pred)
                   | Some s -> Some(Pos.Set.add s     pred))

  let pred_of_succ linfo =
    Pos.Table.iteri linfo.succ
      ~f:(fun ~key ~data ->
            Pos.Set.iter data ~f:(fun pos -> add_pred linfo ~pos ~pred:key))

  let succ_of_pred linfo =
    Pos.Table.iteri linfo.pred
      ~f:(fun ~key ~data ->
            Pos.Set.iter data ~f:(fun pos -> add_succ linfo ~pos ~succ:key))

  let pp_set_pos =
    pp_set pp_pos (fun s -> List.sort ~cmp:compare_pos (Pos.Set.to_list s))

  let pp_pos_table pp_data fmt li_ss =
    List.iter
      (List.sort ~cmp:(fun a b -> compare_pos (fst a) (fst b))
         (Pos.Table.to_alist li_ss))
      ~f:(fun (key,data) ->
            F.fprintf fmt "%a -> %a; " pp_pos key pp_data data)

  let pp fmt li =
    F.fprintf fmt
      "use: %a\ndef: %a\nsucc: %a\npred: %a\nlive_before: %a\nlive_after: %a\n"
      (pp_pos_table pp_set_string) li.use
      (pp_pos_table pp_set_string) li.def
      (pp_pos_table pp_set_pos)    li.succ
      (pp_pos_table pp_set_pos)    li.pred
      (pp_pos_table pp_set_string) li.live_before
      (pp_pos_table pp_set_string) li.live_after

  let string_of_instr = function
    | Binstr(bi)          -> fsprintf "%a"               pp_base_instr bi
    | If(Fcond(fc),_,_)   -> fsprintf "if %a {} else {}" pp_fcond fc
    | While(WhileDo,fc,_) -> fsprintf "while %a {}"      pp_fcond fc
    | While(DoWhile,fc,_) -> fsprintf "do {} while %a;"  pp_fcond fc
    | _                   -> fsprintf "string_of_instr: unexpected instruction"

  let traverse_cfg_backward ~f linfo =
    let visited = Pos.Table.create () in
    let rec go pos =
      f pos;
      Pos.Table.set visited ~key:pos ~data:();
      Pos.Set.iter (Pos.Table.find linfo.pred pos
                       |> Option.value ~default:Pos.Set.empty)
        ~f:(fun p -> if Pos.Table.find visited p = None then go p)
    in
    go return_fun_pos

  let dump ~verbose linfo fname =
    let ctr = ref 1 in
    let visited     = Pos.Table.create () in
    let code_string = Pos.Table.create () in
    let code_id     = Pos.Table.create () in
    let node_succ   = Pos.Table.create () in
    let to_string before pos =
      fsprintf "%s%a: %s %s \\n%a"
        (if before then
            fsprintf "%a\\n"         pp_set_string (get_live_before linfo pos)

         else "")
        pp_pos pos
        (get_str linfo pos)
        (if verbose then
           fsprintf "def=%a use=%a "
              pp_set_string (get_def linfo pos)
              pp_set_string (get_use linfo pos)
         else "")
        pp_set_string (get_live_after linfo pos)
    in
    let sb = Buffer.create 256 in
    let rec collect_basic_block pos =
      match HT.find linfo.succ pos with
      | Some(ss) when false -> (* Set.length ss = 1 -> *)
        let succ_pos = Set.min_elt_exn ss in
        if not (HT.mem visited succ_pos) then (
          begin match HT.find linfo.pred succ_pos with
          | Some(ss) when Set.length ss = 1 ->
            Buffer.add_string sb "\\n";
            Buffer.add_string sb (to_string false succ_pos);
            HT.set visited ~key:succ_pos ~data:();
            collect_basic_block succ_pos
          | None | Some(_) -> pos
          end
        ) else (
          pos
        )
      | None | Some(_) -> pos
    in
    let rec go pos =
      HT.set visited ~key:pos ~data:();
      HT.set code_id ~key:pos ~data:!ctr;
      incr ctr;
      Buffer.clear sb;
      Buffer.add_string sb (to_string true pos);
      let pos' = collect_basic_block pos in
      let s = Buffer.to_bytes sb in
      HT.set code_string ~key:pos ~data:s;
      let succs =
        Pos.Table.find linfo.succ pos'
        |> Option.value ~default:Pos.Set.empty
      in
      HT.set node_succ ~key:pos ~data:succs;
      Set.iter succs
        ~f:(fun p -> if Pos.Table.find visited p = None then go p)
    in
    go enter_fun_pos;
    let g = ref G.empty in
    Pos.Table.iteri node_succ
      ~f:(fun ~key ~data ->
            let to_string pos = HT.find_exn code_string pos in
            g := G.add_vertex !g (HT.find_exn code_id key, to_string key);
            Pos.Set.iter data
              ~f:(fun succ ->
                    g := G.add_edge !g (HT.find_exn code_id key, to_string key)
                                       (HT.find_exn code_id succ, to_string succ)));
    let file = open_out_bin fname in
    Dot.output_graph file !g
end

(* *** CFG traversal *)

let update_liveness linfo changed pos =
  let succs = LI.get_succ linfo pos in
  (* if not (Pos.Set.is_empty (Pos.Set.inter !changed succs)) then ( *)
  let live = ref SS.empty in
    (* compute union of live_before of successors *)
    (* F.printf "updating %a with succs: %a\n" pp_pos pos LI.pp_set_pos succs; *)
  Pos.Set.iter succs
    ~f:(fun spos ->
          let live_s = LI.get_live_before linfo spos in
          live := SS.union !live live_s);
  (* update live_{before,after} of this vertex *)
  let live_after = LI.get_live_after linfo pos in
  if not (SS.equal !live live_after) then changed := true;
  let live_before_old = LI.get_live_before linfo pos in
  let def_s = LI.get_def linfo pos in
  let use_s = LI.get_use linfo pos in
  Pos.Table.set linfo.LI.live_after ~key:pos ~data:!live;
  let live_before = SS.union (SS.diff !live def_s) use_s in
  if not (SS.equal live_before live_before_old) then changed := true;
  Pos.Table.set linfo.LI.live_before ~key:pos ~data:live_before

(* *** Liveness information computation *)

let rec init_liveness_instr linfo ~path ~idx ~exit_p instr =
  let pos = path@[idx] in
  let succ_pos = Option.value exit_p ~default:(path@[idx + 1]) in
  let li_use  = linfo.LI.use  in
  let li_def  = linfo.LI.def  in
  let li_str  = linfo.LI.str  in
  (* set use, def, and str *)
  Pos.Table.set li_use ~key:pos ~data:(use_instr instr);
  Pos.Table.set li_def ~key:pos ~data:(def_instr instr);
  Pos.Table.set li_str ~key:pos ~data:(LI.string_of_instr instr);
  (* set succ and recursively initialize blocks in if and while *)
  match instr with

  | Binstr(_) ->
    LI.add_succ linfo ~pos ~succ:succ_pos

  | If(Fcond(_),s1,s2) ->
    init_liveness_block linfo ~path:(pos@[0]) ~entry_p:pos ~exit_p:succ_pos s1;
    init_liveness_block linfo ~path:(pos@[1]) ~entry_p:pos ~exit_p:succ_pos s2
    
  | While(WhileDo,_,s) ->
    if s=[] then (
      LI.add_succ linfo ~pos ~succ:pos
    ) else (
      LI.add_succ linfo ~pos:(pos@[0;List.length s - 1]) ~succ:pos;
    );
    init_liveness_block linfo ~path:(pos@[0]) ~entry_p:pos ~exit_p:succ_pos s
    
  | While(DoWhile,fc,s) ->
    (* the use is associated with a later node *)
    Pos.Table.set li_use ~key:pos ~data:SS.empty;
    Pos.Table.set li_str ~key:pos ~data:"do {";
    (* add node where test and backwards jump happens *)
    let exit_pos = pos@[1] in
    let exit_str = fsprintf "} while %a;" pp_fcond fc in
    Pos.Table.set li_use ~key:exit_pos ~data:(use_instr instr);
    Pos.Table.set li_def ~key:exit_pos ~data:SS.empty;
    Pos.Table.set li_str ~key:exit_pos ~data:exit_str;
    LI.add_succ linfo ~pos:exit_pos ~succ:pos;
    LI.add_succ linfo ~pos:exit_pos ~succ:succ_pos;
    init_liveness_block linfo ~path:(pos@[0]) ~entry_p:pos ~exit_p:exit_pos s

  | If(Pcond(_),_,_)
  | For(_,_,_,_)     -> failwith "liveness analysis: unexpected instruction"

and init_liveness_block linfo ~path ~entry_p ~exit_p stmt =
  let rec go ~path ~idx = function
    | [] -> failwith "liveness analysis: impossible case"
    | [i] ->
      init_liveness_instr linfo ~path ~idx ~exit_p:(Some exit_p) i.L.l_val
    | i::s ->
      init_liveness_instr linfo ~path ~idx ~exit_p:None i.L.l_val;
      go ~path ~idx:(idx+1) s
  in
  if stmt = [] then (
    (* empty statement goes from entry to exit *)
    LI.add_succ linfo ~pos:entry_p ~succ:exit_p
  ) else (
    (* initialize first node *)
    let first_pos = path@[0] in
    LI.add_succ linfo ~pos:entry_p ~succ:first_pos;
    (* initialize statements *)
    go ~path ~idx:0 stmt
  )

let compute_liveness_stmt linfo stmt ~enter_def ~return_use =
  let ret_pos = LI.return_fun_pos in
  let enter_pos = LI.enter_fun_pos in
  (* initialize return node *)
  let ret_str = fsprintf "return %a" (pp_list "," pp_string) return_use in
  Pos.Table.set linfo.LI.str ~key:ret_pos ~data:ret_str;
  Pos.Table.set linfo.LI.use ~key:ret_pos ~data:(SS.of_list return_use);
  Pos.Table.set linfo.LI.def ~key:ret_pos ~data:(SS.empty);
  (* initialize function args node *)
  let args_str = fsprintf "enter %a" (pp_list "," pp_string) enter_def in
  Pos.Table.set linfo.LI.str ~key:enter_pos ~data:args_str;
  Pos.Table.set linfo.LI.use ~key:enter_pos ~data:(SS.empty);
  Pos.Table.set linfo.LI.def ~key:enter_pos ~data:(SS.of_list enter_def);
  (* compute CFG into linfo *)
  init_liveness_block linfo ~path:[] stmt
    ~entry_p:enter_pos
    ~exit_p:ret_pos;
  (* add backward edges to CFG *)
  LI.pred_of_succ linfo;
  (* set liveness information in live_info *)
  let cont = ref true in
  (* let changed_initial = Pos.Set.singleton LI.return_fun_pos in *)
  let use_return = LI.get_use linfo ret_pos in
  Pos.Table.set linfo.LI.live_before ~key:ret_pos ~data:use_return;
  let n_iter = ref 0 in
  while !cont do
    incr n_iter;
    (* print_endline "iterate"; *)
    (* let changed = ref changed_initial  in *)
    let changed = ref false in
    LI.traverse_cfg_backward ~f:(update_liveness linfo changed) linfo;
    if not !changed then cont := false;
    (* if Pos.Set.equal !changed changed_initial then cont := false; *)
    (* print_endline "iterate done" *)
  done;
  F.printf "---> iterations: %i\n" !n_iter

let compute_liveness_fundef fdef arg_defs =
  let linfo = LI.mk () in
  let stmt = fdef.fd_body in
  compute_liveness_stmt linfo stmt ~enter_def:arg_defs ~return_use:fdef.fd_ret;
  linfo

let compute_liveness_func func =
  let args_def = List.map ~f:(fun (_,n,_) -> n) func.f_args in
  let fdef = match func.f_def with
    | Def fd -> fd
    | Undef  -> failwith "Cannot add liveness annotations to undefined function"
    | Py(_)  -> failwith "Cannot add liveness annotations to python function"
  in
  compute_liveness_fundef fdef args_def

let compute_liveness_modul modul fname =
  match List.find modul.m_funcs ~f:(fun f -> f.f_name = fname) with
  | Some func -> compute_liveness_func func
  | None      -> failwith "compute_liveness: function with given name not found"

(* ** Collect equality and fixed register constraints from +=, -=, :=, ...
 * ------------------------------------------------------------------------ *)

module REGI = struct
  type t = {
    class_of : string        String.Table.t;
    rank_of  : int           String.Table.t;
    fixed    : (int * L.loc) String.Table.t;
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
              ~f:(function | None     -> Some(SS.singleton n)
                           | Some(ss) -> Some(SS.add ss n)));
    classes

  let rank_of rinfo name =
    match HT.find rinfo.rank_of name with
    | None    -> 0
    | Some(r) -> r

  let fix_class rinfo d reg =
    let s = class_of rinfo d.d_name in
    match HT.find rinfo.fixed s with
    | None ->
      HT.set rinfo.fixed ~key:s ~data:(reg,d.d_loc)
    | Some(reg',_) when reg = reg' -> ()
    | Some(reg',loc') ->
      failtype_ loc' "conflicting requirements: %a vs %a for %s"
        X64.pp_int_reg reg' X64.pp_int_reg reg d.d_name

  let union_fixed fixed ~keep:s1 ~merge:s2 =
    match HT.find fixed s1, HT.find fixed s2 with
    | _, None -> ()
    | None, Some(r2) ->
      HT.remove fixed s2;
      HT.set fixed ~key:s1 ~data:r2
    | Some(r1), Some(r2) when r1 = r2 ->
      HT.remove fixed s2; 
    | Some(r1,_), Some(r2,_) ->
      failwith_ "conflicting requirements: %a vs %a for %s and %s"
        X64.pp_int_reg r1 X64.pp_int_reg r2 s1 s2

  let union_class rinfo d1 d2 =
    let root1 = class_of rinfo d1.d_name in
    let root2 = class_of rinfo d2.d_name in
    if root1<>root2 then (
      let rank1 = rank_of rinfo root1 in
      let rank2 = rank_of rinfo root2 in
      match () with
      | _ when rank1 < rank2 ->
        HT.set rinfo.class_of ~key:root1 ~data:root2;
        union_fixed rinfo.fixed ~keep:root2 ~merge:root1
      | _ when rank2 < rank1 ->
        HT.set rinfo.class_of ~key:root2 ~data:root1;
        union_fixed rinfo.fixed ~keep:root1 ~merge:root2
      | _ ->
        HT.set rinfo.class_of ~key:root1 ~data:root2;
        union_fixed rinfo.fixed ~keep:root2 ~merge:root1;
        HT.set rinfo.rank_of  ~key:root2 ~data:(rank2 + 1)
    )

  let pp_fixed fmt (i,_l) = X64.pp_int_reg fmt i

  let pp fmt rinfo =
    F.fprintf fmt
      ("classes: %a\n"^^"ri_fixed: %a\n")
      (pp_ht ", "  "->" pp_string pp_set_string)  (get_classes rinfo)
      (pp_ht ", "  "->" pp_string pp_fixed) rinfo.fixed

end

let reg_info_binstr rinfo bi =
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
      REGI.fix_class rinfo d2 (X64.int_of_reg X64.RAX);
      REGI.fix_class rinfo d1 (X64.int_of_reg X64.RDX)

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

  (* add equality constraint *)
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

let rec reg_info_instr rinfo li =
  let ri_stmt = reg_info_stmt rinfo in
  match li.L.l_val with
  | Binstr(bi)         -> reg_info_binstr rinfo bi
  | While(_,_fc,s)     -> ri_stmt s
  | If(Fcond(_),s1,s2) -> ri_stmt s1; ri_stmt s2

  | If(Pcond(_),_,_)
  | For(_,_,_,_)     -> failwith "register allocation: unexpected instruction"

and reg_info_stmt rinfo stmt =
  List.iter ~f:(reg_info_instr rinfo) stmt

let reg_info_func rinfo func fdef =
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
            REGI.fix_class rinfo (mk_dest_name n Reg U64) (X64.int_of_reg arg_reg))
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
      ~f:(fun (n,ret_reg) -> REGI.fix_class rinfo (mk_dest_name n Reg U64) ret_reg)
  in

  fix_regs_args rinfo;
  fix_regs_ret rinfo;
  reg_info_stmt rinfo fdef.fd_body
  (* F.printf "\n%a\n%!" REGI.pp rinfo *)

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

let assign_reg reg_num denv (conflicts : (unit String.Table.t) String.Table.t) classes rinfo cur_pos name =
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
    if !dbg then F.printf "  in class %s fixed to %a\n%!" cl (pp_opt "-" REGI.pp_fixed) ofixed;
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
                                  | None       -> ()
                                  | Some(ri,_) -> HT.set conflicted_fixed ~key:ri ~data:());
    if !dbg then
      F.printf "  conflicted with fixed %a\n%!"
        (pp_list "," X64.pp_int_reg) (HT.keys conflicted_fixed);
    begin match ofixed with
    | None ->
      let ri = max_not_in reg_num (HT.keys conflicted_fixed) in
      REGI.fix_class rinfo (mk_dest_name cl U64 Reg) ri;
      if !dbg then F.printf "  fixed register to %a\n%!" X64.pp_int_reg ri
    | Some(ri,l) ->
      if HT.mem conflicted_fixed ri then (
        F.printf "\n\nERROR:\n\n%!";
        F.printf "  reg %s in class %s fixed to %a\n%!" name cl (pp_opt "-" REGI.pp_fixed) ofixed;
        F.printf "  conflicted with %a\n%!" (pp_list "," pp_string) (HT.keys conflicted);
        let f n =
          Option.bind (HT.find rinfo.REGI.fixed (REGI.class_of rinfo n))
            (fun (i,_) -> if i = ri then Some (n,i) else None)
        in
        let conflicted_fixed = List.filter_map ~f (HT.keys conflicted) in
        F.printf "  conflicted with fixed %a\n%!"
          (pp_list "," (pp_pair ":" pp_string X64.pp_int_reg)) conflicted_fixed;
        
        failtype_ l "assign_reg: conflict between fixed register"
      )
    end

  | None -> assert false

  | Some(_t,_s) -> ()
    (* F.printf "ignoring %s with %a %s\n" n pp_ty t (string_of_storage s) *)

let assign_regs reg_num denv (conflicts : (unit String.Table.t) String.Table.t) linfo rinfo =
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

let reg_alloc_func reg_num func =
  assert (func.f_call_conv = Extern);
  let rename denv rinfo name =
    match Map.find denv name with
    | None -> assert false
    | Some(U64,Reg) ->
      let cl = REGI.class_of rinfo name in
      let ri = fst @@ HT.find_exn rinfo.REGI.fixed cl in
      fsprintf "r_%i_%a" ri X64.pp_int_reg ri
    | Some(_,_) ->
      name
  in
  let extract_conflicts linfo conflicts ~key:pos ~data:live_set =
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
  in
  let print_time start stop = F.printf "   %fs\n%!" (stop -. start) in

  (* compute equality constraints and fixed constraints *)
  let rinfo = REGI.mk () in
  let t1 = Unix.gettimeofday () in
  F.printf "-> computing equality and fixed constraints\n%!";
  let fd = get_fundef ~err_s:"perform register allocation" func in
  reg_info_func rinfo func fd;
  let t2 = Unix.gettimeofday () in
  print_time t1 t2;

  (* compute liveness information *)
  F.printf "-> computing liveness\n%!";
  let linfo = compute_liveness_func func in
  let conflicts = String.Table.create () in
  let t3 = Unix.gettimeofday () in
  print_time t2 t3;
  F.printf "-> computing conflicts\n%!";
  HT.iteri linfo.LI.live_after ~f:(extract_conflicts linfo conflicts);
  let denv = IT.denv_of_func func (IT.extract_decls func.f_args fd) in
  let t4 = Unix.gettimeofday () in
  print_time t3 t4;
  F.printf "-> assigning registers\n%!";
  assign_regs reg_num denv conflicts linfo rinfo;
  let t5 = Unix.gettimeofday () in
  print_time t4 t5;
  F.printf "-> renaming variables\n%!";
  let func = rename_func (rename denv rinfo) func in
  let t6 = Unix.gettimeofday () in
  print_time t5 t6;
  func
  
let reg_alloc_modul reg_num modul fname =
  map_fun ~f:(reg_alloc_func reg_num) modul fname

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
