open Prog
open Syntax

exception NotSupportedError of Location.t * string

let not_supported_error loc msg =
  raise (NotSupportedError (loc, msg))

exception LogicalError of string

let logical_error msg =
  raise (LogicalError msg)

module F = Format
module B = Bigint
module PP = Pipeline_program

(* -------------------------------------------------------------------- *)

let identifier = ref (-1)

let init_checkpoint () = identifier := -1

let get_fresh_checkpoint () = (incr identifier ; !identifier)

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
      (PP.MemoryAt (u.v_name ^ " + ??")) :: (PP.Register u.v_name) :: reade) (* TODO *)
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
      [PP.MemoryAt (u.v_name ^ " + ??")]) (* TODO *)

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
      then blocs := !current_bloc :: !blocs
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
  !blocs

(* Returns an atomic instruction for the analyzer corresponding to the assign
   instruction x = e at pos l *)
let gassgn_to_pipeline l x e =
  (* Collect all variables read and write by x *)
  let readx, writex = read_write_glv l x in
  (* Collect all variables read by e and the operand*)
  let op, reade = op_read_expr l e in
  PP.to_atomic op (readx @ reade) writex


(* Returns an atomic instruction for the analyzer corresponding to the
   instruction x = o(e) at pos l *)
let gopn_to_pipeline l x o e =
  (* Collect all variables read and write by x *)
  let readx, writex = read_write_glvs l x in
  (* Collect all variables read by e and the operand*)
  let reade = read_exprs l e in
  let charlist = Expr.string_of_sopn o in
  let op = String.init (List.length charlist) (List.nth charlist) in
  PP.to_atomic op (readx @ reade) writex

(* Returns a list of program statements for the analyzer corresponding to the
   statement i *)
let rec gi_to_pipeline i =
  let (l, _) = i.i_loc in 
  match i.i_desc with
  | Cassgn(x, _, _, e) ->
    (* An assignment x = e *)
    [PP.Bloc(-1, [gassgn_to_pipeline l x e])]

  | Copn(x, _, o, e) ->
    (* An assignment x = o(e), x and e are lists *)
    [PP.Bloc(-1, [gopn_to_pipeline l x o e])]

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
      let precond = cblock_to_pipeline c in
      precond @ [ PP.Loop (reade, PP.Seq precond)]

  | Cwhile(_, c, e, c') ->
      let _, reade = op_read_expr l e in
      let precond = cblock_to_pipeline c in
      let body = cblock_to_pipeline c' in
      precond @ [ PP.Loop (reade, PP.Seq (body @ precond))]

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
  PP.Seq (cblock_to_pipeline fd.f_body)


(* -------------------------------------------------------------------- *)

(* Shortcuts for cost variable names *)
let var_name min = if min then "costMin" else "costMax"

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
    | Cassgn (_,_,_,_) -> begin
        if !in_bloc
        then [i]
        else 
            let b = get_fresh_checkpoint () in
            let vmin = (fst config.(b)) in
            let vmax = (snd config.(b)) in
            let instr = get_cost_incr_instr vmin i cmin in
            let instr' = get_cost_incr_instr vmax i cmax in
            in_bloc := true; [instr; instr'; i]
      end
    | Copn (_,_,_,_) -> begin
        if !in_bloc
        then [i]
        else 
            let b = get_fresh_checkpoint () in
            let vmin = (fst config.(b)) in
            let vmax = (snd config.(b)) in
            let instr = get_cost_incr_instr vmin i cmin in
            let instr' = get_cost_incr_instr vmax i cmax in
            in_bloc := true; [instr; instr'; i]
      end
    | Cif(e, c1, c2) -> begin
        in_bloc := false;
        let branch1 = instr_cbloc c1 cmin cmax config in
        let branch2 = instr_cbloc c2 cmin cmax config in
        [
          get_cost_incr_instr 5 i cmax;
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
        (* If there is a precondition, we put its cost first
           and we are no longer in a bloc *)
        let precond_cost =
          if c <> []
          then begin
            in_bloc := false;
            let b = get_fresh_checkpoint () in
            let vmin = (fst config.(b)) in
            let vmax = (snd config.(b)) in
            let instr = get_cost_incr_instr vmin i cmin in
            let instr' = get_cost_incr_instr vmax i cmax in
            [instr; instr']
          end
          else []
        in
        (* Before loop, the jump cost *)
        let instr1 = get_cost_incr_instr 1 i cmin in
        let instr2 = get_cost_incr_instr 6 i cmax in
        (* Jump cost inside the loop *)
        let instr3 = get_cost_incr_instr 1 i cmin in
        let instr4 = get_cost_incr_instr 5 i cmax in
        (* First the body and precondition, possibly in the same bloc *)
        let body = List.flatten (List.map aux (c' @ c)) in
        in_bloc := false;
        precond_cost @ [instr1; instr2] @ [
          {
          i_desc = Cwhile(t,
              c,
              e,
              [instr3; instr4] @ body
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

(* Given a function fd and the cost information per bloc in config,
   returns the instrumented function *)
let instrument config fd =
  let cost_var_min = V.mk (var_name true) Reg (Bty Int) fd.f_loc in
  let cost_var_max = V.mk (var_name false) Reg (Bty Int) fd.f_loc in
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



let instrument_prog (gd, funcs) =
  let functions = List.map fun_to_pipeline funcs in
  Format.eprintf "Program functions : %d@." (List.length functions);
  let current_program = List.hd functions in
    (* For information *)
    Format.printf "All instructions needed by this program:\n@[<h>";
    List.iter (fun i -> Format.printf "%s@ " i) (PP.get_all_instr_in current_program);
    Format.printf "@]@ ";
  let proc = Pipeline.new_processor () in
  let instr_blocs = Pipeline.instrument current_program proc in
  let checkpoints_bounds = extract_checkpoints_values instr_blocs in
  identifier := -1;
  (gd, [instrument checkpoints_bounds (List.hd funcs)])
