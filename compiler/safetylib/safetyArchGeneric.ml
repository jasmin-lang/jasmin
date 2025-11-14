open Jasmin
open Prog
open SafetyExpr
open SafetyVar
open SafetyConstr

(** Generic pseudo-op helpers (architecture-independent) *)
module PseudoOps = struct
  let as_seq1 = function [e] -> e | _ -> assert false
  let as_seq2 = function [e1;e2] -> (e1,e2) | _ -> assert false
  let as_seq3 = function [e1;e2;e3] -> (e1,e2,e3) | _ -> assert false

  let pcast ws e = Papp1 (E.Oword_of_int ws, e)

  let mk_addcarry ws es =
    let el, er, eb = as_seq3 es in
    let w_no_carry = Papp2 (E.Oadd (E.Op_w ws), el, er) in
    let w_carry = Papp2 (E.Oadd (E.Op_w ws),
                         w_no_carry,
                         pcast ws (Pconst (Z.of_int 1))) in

    let eli = Papp1 (E.uint_of_word ws, el)
    and eri = Papp1 (E.uint_of_word ws, er) in
    let w_i = Papp2 (E.Oadd E.Op_int, eli, eri) in
    let pow_ws = Pconst (Z.pow (Z.of_int 2) (int_of_ws ws)) in

    let cf_no_carry = Papp2 (E.Ole E.Cmp_int, pow_ws, w_i) in
    let cf_carry = Papp2 (E.Ole E.Cmp_int,
                          pow_ws,
                          Papp2 (E.Oadd E.Op_int,
                                 w_i,
                                 Pconst (Z.of_int 1))) in

    match eb with
    | Pbool false -> [Some cf_no_carry; Some w_no_carry]
    | Pbool true -> [Some cf_carry; Some w_carry]
    | _ -> [None; None]

  let mk_subcarry ws es =
    let el, er, eb = as_seq3 es in
    let w_no_borrow = Papp2 (E.Osub (E.Op_w ws), el, er) in
    let w_borrow = Papp2 (E.Osub (E.Op_w ws),
                          w_no_borrow,
                          pcast ws (Pconst (Z.of_int 1))) in

    let eli = Papp1 (E.uint_of_word ws, el)
    and eri = Papp1 (E.uint_of_word ws, er) in

    let cf_no_borrow = Papp2 (E.Olt E.Cmp_int, eli, eri) in
    let cf_borrow = Papp2 (E.Ole E.Cmp_int, eli, eri) in

    match eb with
    | Pbool false -> [Some cf_no_borrow; Some w_no_borrow]
    | Pbool true -> [Some cf_borrow; Some w_borrow]
    | _ -> [None; None]

  (** Handle generic pseudo operations *)
  let split_pseudo_op (opn : 'a Sopn.sopn) (es : expr list) : expr option list option =
    match opn with
    | Sopn.Opseudo_op (Osubcarry ws) -> Some (mk_subcarry ws es)
    | Sopn.Opseudo_op (Oaddcarry ws) -> Some (mk_addcarry ws es)
    | Sopn.Opseudo_op (Oswap _ty) ->
      let x, y = as_seq2 es in
      Some [Some y; Some x]
    | _ -> None
end

(** Architecture abstraction for the safety checker *)
module type SafetyArch = sig
  type extended_op

  val pointer_data : Wsize.wsize

  val is_comparison : extended_op Sopn.sopn -> expr list -> (expr * expr) option

  (** Full operation splitting (includes pseudo ops) *)
  val split_opn :
    Wsize.wsize ->
    extended_op Sopn.asmOp ->
    int ->
    extended_op Sopn.sopn ->
    expr list ->
    expr option list

  val post_opn :
    extended_op Sopn.sopn ->
    (int glval) list ->
    expr list ->
    btcons list

  type flags_heur = {
    fh_zf : Mtexpr.t option;
    fh_cf : Mtexpr.t option;
  }

  val opn_heur :
    Wsize.wsize ->
    extended_op Sopn.asmOp ->
    extended_op Sopn.sopn ->
    mvar ->
    expr list ->
    flags_heur option

  val pp_flags_heur : Format.formatter -> flags_heur -> unit
  val get_fh_zf : flags_heur -> Mtexpr.t option
  val get_fh_cf : flags_heur -> Mtexpr.t option
end


