open Arch_decl

let rec product'' l =
  (* We need to do the cross product of our current list and all the others
   * so we define a helper function for that *)
  let rec aux ~acc l1 l2 = match l1, l2 with
  | [], _ | _, [] -> acc
  | h1::t1, h2::t2 ->
      let acc = (h1::h2)::acc in
      let acc = (aux ~acc t1 l2) in
      aux ~acc [h1] t2
  (* now we can do the actual computation *)
  in match l with
  | [] -> []
  | [l1] -> List.map (fun x -> [x]) l1
  | l1::tl ->
      let tail_product = product'' tl in
      aux ~acc:[] l1 tail_product

let x86_condts =
  [ X86_decl.O_ct; NO_ct; B_ct; NB_ct; E_ct; NE_ct; BE_ct; NBE_ct; S_ct; NS_ct; P_ct;
    NP_ct; L_ct; NL_ct; LE_ct; NLE_ct ]

let x86_arg_of_arg_kind = function
  | CAcond -> List.map (fun c -> Condt c) x86_condts
  | CAreg -> [ Reg X86_decl.RSP ]
  | CAregx -> [ Regx X86_decl.MM0 ]
  | CAxmm -> [ XReg X86_decl.XMM0 ]
  | CAmem _ ->
      let addr =
        {
          ad_disp = Word0.wrepr U64 (Conv.cz_of_int 0);
          ad_base = None;
          ad_scale = Conv.nat_of_int 0;
          ad_offset = None;
        }
      in
      [ Addr (Areg addr) ]
  | CAimm _ -> [ Imm(U32, Word0.wrepr U32 (Conv.cz_of_int 0)) ]

let x86_args_of_arg_kinds aks = List.concat_map x86_arg_of_arg_kind aks


let x86_args_of_args_kinds as_ks =
  List.map x86_args_of_arg_kinds as_ks |> product''

let x86_args_of_i_args_kinds i_as_ks = List.concat_map x86_args_of_args_kinds i_as_ks

let pp_suff_x86 name preop suff : string list =
  match preop suff with
  | None -> failwith "ERROR: invalid suffix"
  | Some op ->
      let id =
        instr_desc X86_decl.x86_decl X86_instr_decl.x86_op_decl (None, op)
      in
      let i_as_ks = id_args_kinds X86_decl.x86_decl id in
      let all_args = x86_args_of_i_args_kinds i_as_ks in
      let doit args = id.id_pp_asm args |> Ppasm.pp_name_ext in
      let mapped = List.map doit all_args in
      List.map (fun f -> name ^ ":" ^ String.uppercase_ascii f) mapped

let pp_x86 name pc : string list =
  match pc with
  | Sopn.PrimX86 (suffs, preop) ->
    if suffs = [] then
      [name ^ ":" ^ name]
    else
      List.concat_map (pp_suff_x86 name preop) suffs
  | Sopn.PrimARM _ -> failwith "Bad type!"

let x86_supp_instr =
  List.concat_map (fun (name, pc) -> pp_x86 (Conv.string_of_cstring name) pc) X86_instr_decl.x86_prim_string
  |> List.sort_uniq String.compare

let arm_condts =
  [ Arm_decl.EQ_ct; NE_ct; CS_ct; CC_ct; MI_ct; PL_ct; VS_ct; VC_ct; HI_ct; LS_ct; GE_ct; LT_ct; GT_ct; LE_ct  ]

let arm_arg_of_arg_kind = function
  | CAcond -> List.map (fun c -> Condt c) arm_condts
  | CAreg -> [ Reg Arm_decl.R00 ]
  | CAregx -> []
  | CAxmm -> []
  | CAmem _ ->
      let addr =
        {
          ad_disp = Word0.wrepr U64 (Conv.cz_of_int 0);
          ad_base = None;
          ad_scale = Conv.nat_of_int 0;
          ad_offset = None;
        }
      in
      [ Addr (Areg addr) ]
  | CAimm _ -> [ Imm(U32, Word0.wrepr U32 (Conv.cz_of_int 0)) ]

let arm_args_of_arg_kinds aks = List.concat_map arm_arg_of_arg_kind aks

let arm_args_of_args_kinds as_ks =
  List.map arm_args_of_arg_kinds as_ks |> product''

let arm_args_of_i_args_kinds i_as_ks = List.concat_map arm_args_of_args_kinds i_as_ks

let pp_suff_arm name f a b : string list =
  let op = f a b in
  let id = instr_desc Arm_decl.arm_decl Arm_instr_decl.arm_op_decl (None, op) in
  let i_as_ks = id_args_kinds Arm_decl.arm_decl id in
  let all_args = arm_args_of_i_args_kinds i_as_ks in
  let doit args = id.id_pp_asm args in
  let mapped = List.map doit all_args in
  (* TODO: actually use this and print the expanded instructions. *)
  List.map (fun f -> name ^ ":" ^ name) mapped

let pp_arm name pc : string list =
  match pc with
  | Sopn.PrimX86 _ -> failwith "Bad type!"
  | Sopn.PrimARM (f) -> pp_suff_arm name f true false


let arm_supp_instr =
  List.concat_map (fun (name, pc) -> pp_arm (Conv.string_of_cstring name) pc) Arm_instr_decl.arm_prim_string
  |> List.sort_uniq String.compare


let show_intrinsics asmOp fmt =
  let index =
    function
    | Sopn.PrimX86 (sfx, _) ->
      begin match sfx with
      | [] -> 0
      | PVp _ :: _ -> 1
      | PVx _ :: _ -> 2
      | (PVv _ | PVsv _) :: _ -> 3
      | PVvv _ :: _ -> 4
      end
    | PrimARM _ -> 5
  in
  let headers = [|
      "no size suffix";
      "one optional size suffix, e.g., “_64”";
      "a zero/sign extend suffix, e.g., “_u32u16”";
      "one vector description suffix, e.g., “_4u64”";
      "two vector description suffixes, e.g., “_2u16_2u64”";
      "a flag setting suffix (i.e. “S”) and a condition suffix (i.e. “cc”)"
    |] in
  let intrinsics = Array.make 6 [] in
  List.iter (fun (n, i) ->
      let j = index i in
      intrinsics.(j) <- n :: intrinsics.(j))
    (Pretyping.prim_string asmOp);
  Array.iter2 (fun h m ->
      Format.fprintf fmt "Intrinsics accepting %s:@." h;
      m |>
      List.sort String.compare |>
      List.iter (Format.fprintf fmt " - %s@.");
      Format.fprintf fmt "@."
    ) headers intrinsics


let show_intrinsics asmOp () =
  show_intrinsics asmOp Format.std_formatter


let show_instructions () =
  let instr_list = match !Glob_options.target_arch with
  | X86_64 -> x86_supp_instr
  | ARM_M4 -> arm_supp_instr
  in
  List.iter print_endline instr_list
