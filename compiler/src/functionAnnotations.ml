open Utils
open Prog

(* -------------------------------------------------------------------- *)
let rec pannot_to_annotations (pannot : Syntax.pannotations) : Annotations.annotations =
  List.map pannot_to_annotation pannot

and pannot_to_annotation ((id, pattri) : Syntax.pannotation) : Annotations.annotation =
  (id, Option.map pattri_to_attribute pattri)

and pattri_to_attribute (pattri: Syntax.pattribute) : Annotations.attribute =
  let loc = L.loc pattri in
  L.mk_loc loc (pattri_to_simple_attribute (L.unloc pattri))

and pattri_to_simple_attribute (pattri: Syntax.psimple_attribute) : Annotations.simple_attribute =
  match pattri with
  | PAstring s -> Astring s
  | PAws ws -> Aws ws
  | PAstruct s -> Astruct (pannot_to_annotations s)
  | PAexpr e ->
      match L.unloc e with
      | PEVar id -> Aid (L.unloc id)
      | PEInt ir -> Aint (Syntax.parse_int ir)
      | PEOp1 (`Neg None, {L.pl_desc = PEInt ir}) -> Aint (Z.neg (Syntax.parse_int ir))
      | _ ->
        hierror ~kind:"syntax" ~loc:(Lone (L.loc e))
          "complex expressions not allowed in annotations"

(* -------------------------------------------------------------------- *)
let process_f_annot loc funname f_cc annot =
  let open FInfo in

  let annot = pannot_to_annotations annot in
  let mk_ra = Annot.filter_string_list None ["stack", OnStack; "reg", OnReg] in

  let retaddr_kind =
    let kind = Annot.ensure_uniq1 "returnaddress" mk_ra annot in
    if kind <> None && not (FInfo.is_subroutine f_cc) then
      hierror
        ~loc:(Lone loc)
        ~funname
        ~kind:"unexpected annotation"
        "returnaddress only applies to subroutines";
    kind
  in

  let stack_zero_strategy =

    let strategy =
      let mk_szs = Annot.filter_string_list None Glob_options.stack_zero_strategies in
      let strategy = Annot.ensure_uniq1 "stackzero" mk_szs annot in
      if strategy <> None && not (FInfo.is_export f_cc) then
        hierror
          ~loc:(Lone loc)
          ~funname
          ~kind:"unexpected annotation"
          "stackzero only applies to export functions";
      if Option.is_none strategy then
        !Glob_options.stack_zero_strategy
      else
        strategy
    in

    let size =
      let size = Annot.ensure_uniq1 "stackzerosize" (Annot.wsize None) annot in
      if Option.is_none size then
        !Glob_options.stack_zero_size
      else
        size
    in

    match strategy, size with
    | None, None -> None
    | None, Some _ ->
        warning Always
          (L.i_loc0 loc)
          "\"stackzerosize\" is ignored, since you did not specify a strategy with attribute \"stackzero\"";
        None
    | Some szs, _ -> Some (szs, size)
  in

  { retaddr_kind;
    stack_allocation_size = Annot.ensure_uniq1 "stackallocsize" (Annot.pos_int None) annot;
    stack_size            = Annot.ensure_uniq1 "stacksize"      (Annot.pos_int None) annot;
    stack_align           = Annot.ensure_uniq1 "stackalign"     (Annot.wsize None)   annot;
    max_call_depth        = Annot.ensure_uniq1 "calldepth"      (Annot.pos_int None) annot;
    stack_zero_strategy;
    f_user_annot          = annot;
  }
