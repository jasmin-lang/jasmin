open Prog
open Syntax
open Overlap

exception NotSupportedError of Location.t * string

let not_supported_error loc msg =
  raise (NotSupportedError (loc, msg))

exception LogicalError of string

let logical_error msg =
  raise (LogicalError msg)

module F = Format
module B = Bigint
module PP = Pipeline_program

let use_branch_prediction = true

(* -------------------------------------------------------------------- *)

let identifier = ref (-1)

let init_checkpoint () = identifier := -1

let get_fresh_checkpoint () = (incr identifier ; !identifier)

(* -------------------------------------------------------------------- *)

(* Map from program point *)
module InstrPPMap = Map.Make (struct type t = int let compare = compare end)

module Sope = Set.Make (struct type t = Pipeline_program.operand let compare = compare end)

(* Map from program points to memoryAt used *)
let collect_memoryat = ref InstrPPMap.empty

let add_memoryat pp mem =
    let new_pp_list =
        let previous = (InstrPPMap.find_opt pp !collect_memoryat)
        in match previous with
        | None -> mem
        | Some l -> mem @ l
    in
    collect_memoryat :=
        InstrPPMap.add pp new_pp_list !collect_memoryat

let get_memoryat pp = 
  let at_pp = (InstrPPMap.find_opt pp !collect_memoryat)
  in match at_pp with
  | None -> []
  | Some l -> l

let extract_memoryat instr =
  let filter = List.filter (function
    | Pipeline_program.Value
    | Pipeline_program.Register _ -> false
    | Pipeline_program.MemoryAt _ -> true)
  in
  (filter (Pipeline_program.instr_inputs instr)) @
  (filter (Pipeline_program.instr_outputs instr))

let sort_aliases op memat = (memat, memat) (* TODO *)

(* -------------------------------------------------------------------- *)
(* Name of the operators for the simulator *)

let string_of_op1 = function
  | E.Oint_of_word _ -> F.sprintf "Conv(int)"
  | E.Osignext (szo, _) -> F.sprintf "Conv%ds" (int_of_ws szo)
  | E.Oword_of_int szo
  | E.Ozeroext (szo, _) -> F.sprintf "Conv%du" (int_of_ws szo)
  | E.Olnot _ -> "BNot"
  | E.Onot    -> "Not"
  | E.Oneg _ -> "Neg"

let string_of_op2 = function
  | E.Oand   -> "And"
  | E.Oor    -> "Or"
  | E.Oadd _ -> "Add"
  | E.Omul _ -> "Mult"
  | E.Osub _ -> "Minus"
  | E.Odiv _ -> "Div"
  | E.Omod _ -> "Mod"

  | E.Oland _ -> "BAnd"
  | E.Olor _ -> "BOr"
  | E.Olxor _ -> "BXor"
  | E.Olsr _ -> "ShiftRight"
  | E.Olsl _ -> "ShiftLeft"
  | E.Oasr _ -> "ASR"

  | E.Oeq  _ -> "Eq"
  | E.Oneq _ -> "Neq"
  | E.Olt  _ -> "Le"
  | E.Ole  _ -> "LeEqual"
  | E.Ogt  _ -> "Gt"
  | E.Oge  _ -> "GtEqual"

  | Ovadd _ -> "VAdd"
  | Ovsub _ -> "VSub"
  | Ovmul _ -> "VMult"
  | Ovlsr _ -> "VShiftRight"
  | Ovasr _ -> "VASR"
  | Ovlsl _ -> "VShiftLeft"


(* -------------------------------------------------------------------- *)

(* Returns the operator and read variables of a right-hand expression *)
let rec op_read_expr l = function
  | Pconst _    -> ("MOV", [])
  | Pbool  _    -> ("MOV", [])
  | Parr_init _ -> ("ArrayInit", [])
  | Pvar x      ->
    let u = (L.unloc x)
    in ("MOV", [PP.Register u.v_name])
  | Pglobal (_, g)    -> ("MOV", [PP.Register g])
  | Pget(_, x, e)
  | Pload(_, x, e)    ->
    let _, reade = op_read_expr l e in
    let u = (L.unloc x) in
    ( "MOV",
      (PP.Register u.v_name) :: reade)
  | Papp1(op, e)      ->
    let _, reade = op_read_expr l e in
    ((string_of_op1 op), reade)
  | Papp2(op, e1, e2) ->
    let _, reade1 = op_read_expr l e1 in
    let _, reade2 = op_read_expr l e2 in
    ((string_of_op2 op), reade1 @ reade2)
  | PappN (op, es)    ->
    let reades = read_exprs l es in
    ((Printer.string_of_opN op), reades)
  | Pif(_, _, _, _) ->
    not_supported_error l "Conditional operator not supported"

(* Given a list of expression, returns the variables read *)
and read_exprs l = function
  | [] -> []
  | h :: t ->
    let _, readh = op_read_expr l h in
    let readt = read_exprs l t in
    ( readh @ readt )

(* Returns the variables read and writtens by a left-hand terms *)
let read_write_glv l = function
  | Lnone (_, _) -> ([], [])
  | Lvar x ->
    let u = (L.unloc x)
    in ([], [PP.Register u.v_name])
  | Lmem (_, x, e)
  | Laset (_, x, e) ->
    let _, reade = op_read_expr l e in
    let u = (L.unloc x) in
    ((PP.Register u.v_name) :: reade,
      [])

(* Given left-hand terms returns the variables read and written *)
let rec read_write_glvs l = function
  | [] -> ([], [])
  | h :: t ->
    let readh, writeh = read_write_glv l h in
    let readt, writet = read_write_glvs l t in
    ( readh @ readt, writeh @ writet )

(* -------------------------------------------------------------------- *)

(* An atomic instruction, corresponding to one operation.
   No control-flow structures*)
let is_atomic i =
  match i.i_desc with
    | Cassgn (_,_,_,_)
    | Copn (_,_,_,_) -> true
    | _ -> false

(* Returns a list of lists of instructions.
   Instructions in the same sub-list form a bloc of
   atomic instructions.
   Control-flow structures are each in their own sub-list. *)
let blockify c =
  let blocs = ref [] in
  let current_bloc = ref [] in
  let in_bloc = ref false in
  let end_current_bloc () =
      if !current_bloc <> []
      then blocs := (List.rev !current_bloc) :: !blocs
  in
  let aux i =
    if is_atomic i then begin
        (* Atomic continues the current bloc *)
        if !in_bloc
        then current_bloc := i :: !current_bloc
        else begin
          end_current_bloc ();
          current_bloc := [i];
          in_bloc := true
        end
      end
    else begin
        (* Control-flow structures ends current bloc *)
        end_current_bloc ();
        blocs := [i] :: !blocs;
        current_bloc := [];
        in_bloc := false
      end
  in
  List.iter aux c;
  end_current_bloc ();
  List.rev !blocs

(* Returns an atomic instruction for the analyzer corresponding to the assign
   instruction x = e at pos l *)
let gassgn_to_pipeline l pp x e aa ma =
  (* Collect all variables read and write by x *)
  let readx, writex = read_write_glv l x in
  (* Collect all variables read by e and the operand*)
  let op, reade = op_read_expr l e in
  let memat = get_memoryat pp in
  let (input_alias_always, output_alias_always) = sort_aliases op aa in
  let (input_alias_maybe, output_alias_maybe) = sort_aliases op ma in
  let pipeline_instr =
    PP.to_atomic
      op
      (readx @ reade @ input_alias_always)
      (writex @ output_alias_always)
      input_alias_maybe
      output_alias_maybe
  in
  add_memoryat pp (extract_memoryat pipeline_instr);
  pipeline_instr


(* Returns an atomic instruction for the analyzer corresponding to the
   instruction x = o(e) at pos l *)
let gopn_to_pipeline l pp x o e aa ma =
  (* Collect all variables read and write by x *)
  let readx, writex = read_write_glvs l x in
  (* Collect all variables read by e and the operand*)
  let reade = read_exprs l e in
  let charlist = Expr.string_of_sopn o in
  let op = String.init (List.length charlist) (List.nth charlist) in
  let (input_alias_always, output_alias_always) = sort_aliases op aa in
  let (input_alias_maybe, output_alias_maybe) = sort_aliases op ma in
  let pipeline_instr =
    PP.to_atomic
      op
      (readx @ reade @ input_alias_always)
      (writex @ output_alias_always)
      input_alias_maybe
      output_alias_maybe
  in
  add_memoryat pp (extract_memoryat pipeline_instr);
  pipeline_instr

let mem_at_set pps =
  let list_pp = Utils.Sint.elements pps in
  let lists_of_mems = List.map get_memoryat list_pp in
  Sope.of_list (List.concat lists_of_mems)

(* Returns a list of program statements for the analyzer corresponding to the
   statement i *)
let rec gi_to_pipeline i =
  let (l, _) = i.i_loc in 
  match i.i_desc with
  | Cassgn(x, _, _, e) ->
    let pp = (snd i.i_info).program_point in
    let always_alias_pps = (snd i.i_info).always_overlaps in
    let always_alias_mem = Sope.elements (mem_at_set always_alias_pps) in
    let never_alias_pps = (snd i.i_info).never_overlaps in
    let never_alias_mem = mem_at_set never_alias_pps in
    let all_alias_pps = (snd i.i_info).overlaps_checked in
    let all_alias_mem = mem_at_set all_alias_pps in
    let may_alias_mem =
      Sope.elements (Sope.diff all_alias_mem never_alias_mem)
    in
    (* An assignment x = e *)
    [PP.Bloc(-1, [gassgn_to_pipeline l pp x e always_alias_mem may_alias_mem])]

  | Copn(x, _, o, e) ->
    let pp = (snd i.i_info).program_point in
    let always_alias_pps = (snd i.i_info).always_overlaps in
    let always_alias_mem = Sope.elements (mem_at_set always_alias_pps) in
    let never_alias_pps = (snd i.i_info).never_overlaps in
    let never_alias_mem = mem_at_set never_alias_pps in
    let all_alias_pps = (snd i.i_info).overlaps_checked in
    let all_alias_mem = mem_at_set all_alias_pps in
    let may_alias_mem =
      Sope.elements (Sope.diff all_alias_mem never_alias_mem)
    in
    (* An assignment x = o(e), x and e are lists *)
    [PP.Bloc(-1, [gopn_to_pipeline l pp x o e always_alias_mem may_alias_mem])]

  | Cif(e, c1, c2) ->
      let _, reade = op_read_expr l e in
      let then_br = cblock_to_pipeline c1 in
      let else_br = cblock_to_pipeline c2 in
      [PP.Cond (reade, PP.Seq then_br, PP.Seq else_br)]

  | Cfor(_, _, _) ->
    not_supported_error l "For-Loop not supported yet"

  | Cwhile(_, [], e, c) ->
      let _, reade = op_read_expr l e in
      let body = cblock_to_pipeline c in
      [PP.Loop (reade, PP.Seq body)]

  | Cwhile(_, c, e, []) ->
      let _, reade = op_read_expr l e in
      let precond_pre = cblock_to_pipeline c in
      let precond_in = cblock_to_pipeline c in
      precond_pre @ [ PP.Loop (reade, PP.Seq precond_in)]

  | Cwhile(_, c, e, c') ->
      let _, reade = op_read_expr l e in
      let precond_pre = cblock_to_pipeline c in
      let body = cblock_to_pipeline c' in
      let precond_in = cblock_to_pipeline c in
      precond_pre @ [ PP.Loop (reade, PP.Seq (body @ precond_in))]

  | Ccall(_, _, _, _) ->
    not_supported_error l "Function call not supported"


(* Returns a list of program statements for the analyzer corresponding to the
   list of statements c *)
and cblock_to_pipeline c =
  (* Decomposed into bloc *)
  let blocs = blockify c in
  let bloc_to_pipeline b = match b with
    | [h]
    | h :: _ when (is_atomic h) ->
      let llist = List.map gi_to_pipeline b in
      let list = List.flatten llist in (* a list of bloc *)
      let list_instr = List.map
        (function 
        | PP.Bloc (_, [i]) -> i
        | _ -> assert false)
        list
      in
      PP.Bloc(get_fresh_checkpoint (), list_instr)
    | [i] -> PP.Seq (gi_to_pipeline i)
    | _ -> assert false
  in
  List.map bloc_to_pipeline blocs

(* Returns a program statement for the analyzer corresponding to the
   body of function fd *)
let fun_to_pipeline fd =
  PP.Seq (cblock_to_pipeline fd.annot_stmt)


(* -------------------------------------------------------------------- *)

(* Shortcuts for cost variable names *)
let var_name min = if min then "costMin" else "costMax"

let max_latency =
  Pipeline.PipelineMap.fold
    (fun _ -> fun l -> fun m -> max l m)
    !Pipeline.pipeline_to_latency
    0

let jump_latency = 
  let pipeline_jump = List.hd (Pipeline.pipelines_for (Pipeline_program.to_atomic "Jump" [] [] [] [])) in
  Pipeline.PipelineMap.find pipeline_jump !Pipeline.pipeline_to_latency

(* Get a jasmin instruction preceeding instr i to initialize the cost variable
   cost_var by value *)
let get_cost_incr_init i cost_var =
  let loc_cost_var = (L.mk_loc (fst i.i_loc) cost_var) in
  let instr_desc = Cassgn(
      Lvar loc_cost_var,
      AT_none, 
      Bty Int, 
      Pconst (Bigint.of_int 0))
  in
  {
    i_desc = instr_desc;
    i_loc = i.i_loc;
    i_info = i.i_info
  }

(* Get a jasmin instruction following instr i to increment the cost variable
   cost_var by value *)
let get_cost_incr_instr value i cost_var =
  let loc_cost_var = (L.mk_loc (fst i.i_loc) cost_var) in
  let instr_desc = Cassgn(
      Lvar loc_cost_var,
      AT_none, 
      Bty Int, 
      Papp2(Oadd Op_int, Pvar loc_cost_var, Pconst (Bigint.of_int value)))
  in
  {
    i_desc = instr_desc;
    i_loc = i.i_loc;
    i_info = i.i_info
  }

(* Given a sequence of jasmin statements c, the cost variables cmin and cmax,
   and the cost information per bloc in config, return an instrumented sequence
   of jasmin statements. *)
let rec instr_cbloc c cmin cmax config =
  let in_bloc = ref false in
  let rec aux i =
    match i.i_desc with
    | Cassgn (_,_,_,_)
    | Copn (_,_,_,_) -> begin
        if !in_bloc
        then [i]
        else 
            let b = get_fresh_checkpoint () in
            let vmin = (fst config.(b)) in
            let vmax = (snd config.(b)) in
            let instr = get_cost_incr_instr vmin i cmin in
            let instr' = get_cost_incr_instr vmax i cmax in
            Format.eprintf "Bloc %d is instrumented@." b;
            in_bloc := true; [instr; instr'; i]
      end
    | Cif(e, c1, c2) -> begin
        in_bloc := false;
        let branch1 = instr_cbloc c1 cmin cmax config in
        let branch2 = instr_cbloc c2 cmin cmax config in
        let branch_cost =
          if !Glob_options.pipeline_branch_predictor
          then [get_cost_incr_instr jump_latency i cmax]
          else [
            get_cost_incr_instr jump_latency i cmin;
            get_cost_incr_instr jump_latency i cmax
          ]
        in
        in_bloc := false;
        branch_cost @
        [
          {
          i_desc = Cif(e,
              branch1,
              branch2
            );
          i_loc = i.i_loc;
          i_info = i.i_info
        }]
      end
    | Cwhile(t, c, e, c') -> begin
        (* If there is a precondition, we put its cost first *)
        let precond_cost_pre =
          if c <> []
          then begin
            let b = get_fresh_checkpoint () in
            let vmin = (fst config.(b)) in
            let vmax = (snd config.(b)) in
            let instr = get_cost_incr_instr vmin i cmin in
            let instr' = get_cost_incr_instr vmax i cmax in
            Format.eprintf "Bloc %d is instrumented (first precond)@." b;
            [instr; instr']
          end
          else []
        in
        (* Before loop, the jump costs *)
        let pre_loop_cost =
          if !Glob_options.pipeline_branch_predictor
          then (* In the best case, the simple branch predictor predicts correctly all jumps , and in the worts case all but two (first enter and first exit. This is an overapproximation is the program never enters the body. *)
            [get_cost_incr_instr (2 * jump_latency) i cmax]
          else
            [
              get_cost_incr_instr jump_latency i cmin;
              get_cost_incr_instr jump_latency i cmax
            ]
        in
        (* Jump cost inside the loop *)
        let in_loop_cost =
          if !Glob_options.pipeline_branch_predictor
          then  []
          else
            [
              get_cost_incr_instr jump_latency i cmin;
              get_cost_incr_instr jump_latency i cmax
            ]
        in
        in_bloc := false;
        (* First the body and precondition, possibly in the same bloc *)
        let body = List.flatten (List.map aux c') in
        (* *)
        let precond_cost_in =
          if c <> []
          then begin
            let b = get_fresh_checkpoint () in
            let vmin = (fst config.(b)) in
            let vmax = (snd config.(b)) in
            let instr = get_cost_incr_instr vmin i cmin in
            let instr' = get_cost_incr_instr vmax i cmax in
            Format.eprintf "Bloc %d is instrumented (body precond)@." b;
            [instr; instr']
          end
          else []
        in
        in_bloc := false;
        precond_cost_pre @ pre_loop_cost @ [
          {
          i_desc = Cwhile(t,
              c,
              e,
              in_loop_cost @ body @ precond_cost_in
            );
          i_loc = i.i_loc;
          i_info = i.i_info
        }]
      end
    | _ -> 
      let (l, _) = i.i_loc in 
      not_supported_error l "Unsupported"
  in
  List.flatten (List.map aux c)

let cost_var_min = V.mk (var_name true) Reg (Bty Int) Location._dummy
let cost_var_max = V.mk (var_name false) Reg (Bty Int) Location._dummy

(* Given a function fd and the cost information per bloc in config,
   returns the instrumented function *)
let instrument config fd =
  let init_min = get_cost_incr_init (List.hd fd.f_body) cost_var_min in
  let init_max = get_cost_incr_init (List.hd fd.f_body) cost_var_max in
  let instrumented = {
    f_loc   = fd.f_loc;
    f_cc    = fd.f_cc;
    f_name  = fd.f_name;
    f_tyin  = fd.f_tyin;
    f_args  = fd.f_args;
    f_body  = [init_min ; init_max] @ (instr_cbloc fd.f_body cost_var_min cost_var_max config);
    f_tyout = fd.f_tyout;
    f_ret   = fd.f_ret
  } in
  instrumented

(* Given a symbolic program p with instrumented bloc, returns the cost 
   information per bloc *)
let extract_checkpoints_values p =
  let costs = Array.make (!identifier + 1) (0,0) in
  let rec aux = function
  | Pipeline.ISkip -> ()
  | Pipeline.IBloc (c, min, max) -> costs.(c) <- (min, max)
  | Pipeline.ISeq l -> List.iter aux l
  | Pipeline.ICond (cif, celse) -> begin
        aux cif;
        aux celse
    end
  | Pipeline.ILoop c -> aux c
  in
  aux p;
  costs



let instrument_prog (gd, funcs) overlap naive =
  let current_function = List.hd funcs in
  let converted_function = Pipeline_program.compact (fun_to_pipeline overlap) in
  let proc = Pipeline.new_processor () in
  let instr_blocs =
    if naive
    then Pipeline.naive_instrument converted_function
    else Pipeline.instrument converted_function proc
  in
  let checkpoints_bounds = extract_checkpoints_values instr_blocs in
  identifier := -1;
  (gd, [instrument checkpoints_bounds current_function])
