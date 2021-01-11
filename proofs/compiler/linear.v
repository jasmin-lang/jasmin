(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Syntax and semantics of the linear language *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.
Import Relations.

Require Import expr compiler_util x86_variables.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
(* --------------------------------------------------------------------------- *)
(* Syntax                                                                      *)

Variant linstr_r :=
  | Lopn   : lvals -> sopn -> pexprs -> linstr_r
  | Lalign : linstr_r
  | Llabel : label -> linstr_r
  | Lgoto  : remote_label -> linstr_r
  | Ligoto : pexpr -> linstr_r (* Absolute indirect jump *)
  | LstoreLabel : lval -> label -> linstr_r
  | Lcond  : pexpr -> label -> linstr_r
.

Arguments Llabel _%positive_scope.

Record linstr : Type := MkLI { li_ii : instr_info; li_i : linstr_r }.

Definition lcmd := seq linstr.

Definition is_label (lbl: label) (i:linstr) : bool :=
  match i.(li_i) with
  | Llabel lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (c : seq linstr) :=
  let idx := seq.find (is_label lbl) c in
  if idx < size c then ok idx else type_error.

Record lfundef := LFundef {
 lfd_align : wsize;
 lfd_tyin : seq stype;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_tyout : seq stype;
 lfd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
 lfd_export: bool;
}.

Definition signature_of_lfundef (lfd: lfundef) : function_signature :=
  (lfd_tyin lfd, lfd_tyout lfd).

Record lprog :=
 {  lp_rip   : Ident.ident;
    lp_globs : seq u8;
    lp_funcs : seq (funname * lfundef) }.




(* --------------------------------------------------------------------------- *)
Section PROG.
Context (p:sprog) (extra_free_registers: instr_info -> option var).

Section WRITE1.

  Context (writefun: funname -> Sv.t).

  Definition writefun_ra (fn:funname) :=
    let ra :=
      match get_fundef (p_funcs p) fn with
      | None => Sv.empty
      | Some fd =>
        match fd.(f_extra).(sf_return_address) with
        | RAnone | RAstack _ => Sv.empty
        | RAreg ra => Sv.singleton ra
        end
      end in
    Sv.union (writefun fn) ra.

  Fixpoint write_i_rec s i :=
    match i with
    | Cassgn x _ _ _  => vrv_rec s x
    | Copn xs _ _ _   => vrvs_rec s xs
    | Cif   _ c1 c2   => foldl write_I_rec (foldl write_I_rec s c2) c1
    | Cfor  x _ c     => foldl write_I_rec (Sv.add x s) c
    | Cwhile _ c _ c' => foldl write_I_rec (foldl write_I_rec s c') c
    | Ccall _ _ fn _  => writefun_ra fn
    | Ccopy x _ => vrv_rec s x
    end
  with write_I_rec s i :=
    match i with
    | MkI ii i =>
      let result := write_i_rec s i in
      if extra_free_registers ii is Some r
      then Sv.add r result
      else result
    end.

  Definition write_c := foldl write_I_rec (Sv.empty).

  Definition write_fd (fd:sfundef) := write_c fd.(f_body).

End WRITE1.

(* We start by initialising the map of writefun, this does not need to be trusted *)

Section WMAP.

Definition get_wmap (wmap : Mp.t Sv.t) (fn:funname) := odflt Sv.empty (Mp.get wmap fn).

Definition mk_wmap := 
  foldr (fun ffd wmap => 
           let: (f,fd) := ffd in
           let w := write_fd (get_wmap wmap) fd in
           Mp.set wmap f w) (Mp.empty _) p.(p_funcs).

Definition check_wmap (wmap:Mp.t Sv.t) := 
  all (fun ffd => Sv.subset (write_fd (get_wmap wmap) ffd.2) (get_wmap wmap ffd.1)) (p_funcs p).

End WMAP.

Section CHECK.

  Section CHECK_c.

    Context (check_i: instr -> ciexec unit).

    Fixpoint check_c (c:cmd) : ciexec unit :=
      match c with
      | [::] => ok tt
      | i::c => check_c c >> check_i i
      end.

  End CHECK_c.

  Section CHECK_i.

  Context (this: funname) (stack_align : wsize).

  Fixpoint check_i (i:instr) : ciexec unit :=
    let (ii,ir) := i in
    match ir with
    | Cassgn x tag ty e =>
      if ty is sword sz then ok tt
      else cierror ii (Cerr_linear "assign not a word")
    | Copn xs tag o es =>
      ok tt
    | Cif b c1 c2 =>
      check_c check_i c1 >> check_c check_i c2
    | Cfor _ _ _ =>
      cierror ii (Cerr_linear "for found in linear")
    | Cwhile _ c e c' =>
      if e == Pbool false then check_c check_i c
      else check_c check_i c >> check_c check_i c'
    | Ccall _ xs fn es =>
      if fn == this then cierror ii (Cerr_linear "call to self") else
      if get_fundef (p_funcs p) fn is Some fd then
        Let _ := assert (sf_return_address (f_extra fd) != RAnone)
          (ii, Cerr_one_varmap "nowhere to store the return address") in
        Let _ := assert (sf_align (f_extra fd) <= stack_align)%CMP
          (ii, Cerr_linear "caller need alignment greater than callee") in
        ok tt
      else cierror ii (Cerr_linear "call to unknown function")
    | Ccopy x e =>
      ok tt
    end.

  End CHECK_i.

  Definition check_fd (ffd:sfun_decl) :=
    let (fn,fd) := ffd in
    let e := fd.(f_extra) in
    let stack_align := e.(sf_align) in
    Let _ := add_finfo fn fn (check_c (check_i fn stack_align) fd.(f_body)) in
    Let _ := assert ((e.(sf_return_address) != RAnone) || (all (λ '(x, _), is_word_type x.(vtype) != None) e.(sf_to_save))) (Ferr_fun fn (Cerr_linear "bad to-save")) in
    Let _ := assert ((sf_return_address e != RAnone) || (sf_save_stack e != SavedStackNone) || ((stack_align == U8) && (sf_stk_sz e == 0) && (sf_stk_extra_sz e == 0))) (Ferr_fun fn (Cerr_linear "bad save-stack")) in
    ok tt.

  Definition check_prog := 
    Let _ := mapM check_fd (p_funcs p) in
    ok tt.

End CHECK.
  
                           
(* --------------------------------------------------------------------------- *)
(* Translation                                                                 *)

Notation "c1 ';;' c2" :=  (let: (lbl,lc) := c2 in c1 lbl lc)
   (at level 26, right associativity).

Notation "c1 '>;' c2" :=  (let: (lbl,lc) := c2 in (lbl, c1::lc))
   (at level 26, right associativity).

Section LINEAR_C.

  Variable linear_i : instr -> label -> lcmd -> label * lcmd.

  Fixpoint linear_c (c:cmd) (lbl:label) (lc:lcmd) :=
    match c with
    | [::] => (lbl, lc)
    | i::c =>
      linear_i i ;; linear_c c lbl lc
    end.

End LINEAR_C.

Definition next_lbl lbl := (lbl + 1)%positive.

Fixpoint snot e :=
  match e with
  | Papp1 Onot e => e
  | Papp2 Oand e1 e2 => Papp2 Oor (snot e1) (snot e2)
  | Papp2 Oor e1 e2 => Papp2 Oand (snot e1) (snot e2)
  | Pif t e e1 e2 => Pif t e (snot e1) (snot e2)
  | Pbool b => Pbool (~~ b)
  | _ => Papp1 Onot e
  end.

Definition add_align ii a (lc:lcmd) :=
  match a with
  | NoAlign => lc
  | Align   =>  MkLI ii Lalign :: lc
  end.

Definition align ii a (p:label * lcmd) : label * lcmd :=
  (p.1, add_align ii a p.2).

Section FUN.

Context (fn: funname) (fn_align: wsize).

Let rsp : var := var_of_register RSP.
Let rspi : var_i := VarI rsp xH.
Let rspg : gvar := Gvar rspi Slocal.

(** Total size of a stack frame: local variables, extra and padding. *)
Definition stack_frame_allocation_size (e: stk_fun_extra) : Z :=
  round_ws e.(sf_align) (sf_stk_sz e + sf_stk_extra_sz e).

Definition allocate_stack_frame (free: bool) (ii: instr_info) (sz: Z) : lcmd :=
  if sz == 0%Z then [::]
  else
    [:: let m i := {| li_ii := ii ; li_i := i |} in
        m (Lopn [:: Lvar rspi] (Ox86 (LEA Uptr))
                [:: Papp2 ((if free then Oadd else Osub) (Op_w Uptr))
                    (Pvar rspg)
                    (cast_const sz)
          ])
    ].

Definition eflags := Eval vm_compute in List.map (λ x, Lvar (VarI (var_of_flag x) xH)) [:: OF ; CF ; SF ; PF ; ZF ].

Definition ensure_rsp_alignment ii (al: wsize) : linstr :=
  MkLI ii (Lopn (eflags ++ [:: Lvar rspi ]) (Ox86 (AND Uptr)) [:: Pvar rspg ; Papp1 (Oword_of_int Uptr) (Pconst (- wsize_size al)) ]).

Definition push_to_save ii (to_save: seq (var * Z)) : lcmd :=
  List.map (λ '(x, ofs),
            if is_word_type x.(vtype) is Some ws
            then MkLI ii (Lopn [:: Lmem ws rspi (cast_const ofs) ] (Ox86 (MOV ws)) [:: Pvar {| gv := VarI x xH ; gs := Slocal |} ])
            else MkLI ii Lalign (* absurd case *))
           to_save.

Definition pop_to_save ii (to_save: seq (var * Z)) : lcmd :=
  List.map (λ '(x, ofs),
            if is_word_type x.(vtype) is Some ws
            then MkLI ii (Lopn [:: Lvar (VarI x xH) ] (Ox86 (MOV ws)) [:: Pload ws rspi (cast_const ofs) ])
            else MkLI ii Lalign (* absurd case *))
           to_save.

Fixpoint linear_i (i:instr) (lbl:label) (lc:lcmd) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn x _ ty e => 
    if ty is sword sz
    then
      let op := if (sz ≤ U64)%CMP then (MOV sz) else (VMOVDQU sz) in
      (lbl, MkLI ii (Lopn [:: x ] (Ox86 op) [:: e]) :: lc)
    else (lbl, lc)
  | Copn xs _ o es => (lbl, MkLI ii (Lopn xs o es) :: lc)

  | Cif e [::] c2 =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond e L1) >; linear_c linear_i c2 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 [::] =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond (snot e) L1) >; linear_c linear_i c1 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 c2 =>
    let L1 := lbl in
    let L2 := next_lbl L1 in
    let lbl := next_lbl L2 in
                           MkLI ii (Lcond e L1) >;
                           linear_c linear_i c2 ;;
                           MkLI ii (Lgoto (fn, L2)) >;
    MkLI ii (Llabel L1) >; linear_c linear_i c1 lbl
   (MkLI ii (Llabel L2) :: lc)

  | Cwhile a c e c' =>
    match is_bool e with
    | Some true =>
      let L1 := lbl in
      let lbl := next_lbl L1 in
      align ii a (
      MkLI ii (Llabel L1) >; linear_c linear_i c ;;
                             linear_c linear_i c' lbl
                             (MkLI ii (Lgoto (fn, L1)) :: lc))

    | Some false =>
      linear_c linear_i c lbl lc

    | None =>
      match c' with
      | [::] =>
      let L1 := lbl in
      let lbl := next_lbl L1 in
      align ii a (MkLI ii (Llabel L1) >; linear_c linear_i c lbl
                             (MkLI ii (Lcond e L1) :: lc))
      | _ =>
      let L1 := lbl in
      let L2 := next_lbl L1 in
      let lbl := next_lbl L2 in
                             MkLI ii (Lgoto (fn, L1)) >;
      align ii a (MkLI ii (Llabel L2) >; linear_c linear_i c' ;;
      MkLI ii (Llabel L1) >; linear_c linear_i c lbl
                             (MkLI ii (Lcond e L2) :: lc))
      end
    end

  | Ccall _ xs fn' es =>
    if get_fundef (p_funcs p) fn' is Some fd then
      let e := f_extra fd in
      let ra := sf_return_address e in
      if ra == RAnone then (lbl, lc)
      else
        let sz := stack_frame_allocation_size e in
        let before := allocate_stack_frame false ii sz in
        let after := allocate_stack_frame true ii sz in
        let lret := lbl in
        let lbl := next_lbl lbl in
        let lcall := (fn', if fn' == fn then (* absurd case *) lret else xH (* entry point *)) in
        match sf_return_address e with
        | RAreg ra =>
          (lbl, before ++ MkLI ii (LstoreLabel (Lvar (VarI ra xH)) lret) :: MkLI ii (Lgoto lcall) :: MkLI ii (Llabel lret) :: after ++ lc)
        | RAstack z =>
          if extra_free_registers ii is Some ra
          then (lbl,
                before ++
                       MkLI ii (LstoreLabel (Lvar (VarI ra xH)) lret) ::
                       MkLI ii (Lopn [::Lmem Uptr rspi (cast_const z)] (Ox86 (MOV Uptr)) [:: Pvar {| gv := VarI ra xH ; gs := Slocal |} ]) ::
                       MkLI ii (Lgoto lcall) :: MkLI ii (Llabel lret) :: after ++ lc)
          else (lbl, lc)
        | RAnone => (lbl, lc)
        end
    else (lbl, lc )
  | Cfor _ _ _ => (lbl, lc)
  | Ccopy _ _ => (lbl, lc)
  end.

Definition linear_fd (fd: sfundef) :=
  let e := fd.(f_extra) in
  let: (tail, head, lbl) :=
     match sf_return_address e with
     | RAreg r => ([:: MkLI xH (Ligoto (Pvar {| gv := VarI r xH ; gs := Slocal |})) ], [:: MkLI xH (Llabel 1) ], 2%positive)
     | RAstack z => ([:: MkLI xH (Ligoto (Pload Uptr rspi (cast_const z))) ], [:: MkLI xH (Llabel 1) ], 2%positive)
     | RAnone =>
       match sf_save_stack e with
       | SavedStackNone => ([::], [::], 1%positive)
       | SavedStackReg x =>
         let r := VarI x xH in
         (pop_to_save xH e.(sf_to_save) ++ [:: MkLI xH (Lopn [:: Lvar rspi ] (Ox86 (MOV Uptr)) [:: Pvar {| gv := r ; gs := Slocal |} ]) ],
          [:: MkLI xH (Lopn [:: Lvar r ] (Ox86 (MOV Uptr)) [:: Pvar rspg ] ) ]
          ++ allocate_stack_frame false xH (sf_stk_sz e + sf_stk_extra_sz e)
          ++ ensure_rsp_alignment xH e.(sf_align)
          :: push_to_save xH e.(sf_to_save), (** FIXME: here to_save is always empty *)
          1%positive)
       | SavedStackStk ofs =>
         let rax := VarI (var_of_register RAX) xH in
         (pop_to_save xH e.(sf_to_save) ++ [:: MkLI xH (Lopn [:: Lvar rspi ] (Ox86 (MOV Uptr)) [:: Pload Uptr rspi (cast_const ofs) ]) ],
          [:: MkLI xH (Lopn [:: Lvar rax ] (Ox86 (MOV Uptr)) [:: Pvar rspg ] ) ]
          ++ allocate_stack_frame false xH (sf_stk_sz e + sf_stk_extra_sz e)
          ++ ensure_rsp_alignment xH e.(sf_align)
          :: MkLI xH (Lopn [:: Lmem Uptr rspi (cast_const ofs) ] (Ox86 (MOV Uptr)) [:: Pvar {| gv := rax ; gs := Slocal |} ])
          :: push_to_save xH e.(sf_to_save),
          1%positive)
       end
     end
  in
  let fd' := linear_c linear_i (f_body fd) lbl tail in
  let is_export := sf_return_address e == RAnone in
  let res := if is_export then f_res fd else [::] in
  LFundef (sf_align e) (f_tyin fd) (f_params fd) (head ++ fd'.2) (f_tyout fd) res
              is_export.

End FUN.

Definition linear_prog : cfexec lprog :=
  Let _ := check_prog in
  Let _ := assert (size p.(p_globs) == 0)
             (Ferr_msg (Cerr_linear "invalid p_globs, please report")) in
  let funcs := map (fun '(f,fd) => (f, linear_fd f fd)) p.(p_funcs) in
  ok {| lp_rip   := p.(p_extra).(sp_rip);
        lp_globs := p.(p_extra).(sp_globs);
        lp_funcs := funcs |}.

End PROG.

Module Eq_linstr.
  Definition eqb_r i1 i2 :=
    match i1, i2 with
    | Lopn lv1 o1 e1, Lopn lv2 o2 e2 => (lv1 == lv2) && (o1 == o2) && (e1 == e2)
    | Lalign, Lalign => true
    | Llabel l1, Llabel l2 => l1 == l2
    | Lgoto l1, Lgoto l2 => l1 == l2
    | Ligoto e1, Ligoto e2 => e1 == e2
    | LstoreLabel lv1 lbl1, LstoreLabel lv2 lbl2 => (lv1 == lv2) && (lbl1 == lbl2)
    | Lcond e1 l1, Lcond e2 l2 => (e1 == e2) && (l1 == l2)
    | _, _ => false
    end.

  Lemma eqb_r_axiom : Equality.axiom eqb_r.
  Proof.
    case => [lv1 o1 e1||l1|l1|e1|lv1 l1|e1 l1] [lv2 o2 e2||l2|l2|e2|lv2 l2|e2 l2] //=;try by constructor.
    + apply (@equivP (((lv1 == lv2) && (o1 == o2)) /\ e1 == e2 ));first by apply andP.
      by split => [ [] /andP [] /eqP -> /eqP -> /eqP -> //| [] -> -> ->];rewrite !eqxx.
    + by apply: (equivP eqP); split; congruence.
    + by apply: (equivP eqP); split; congruence.
    + by apply: (equivP eqP); split; congruence.
    + apply: (equivP andP); split.
      * by case=> /eqP <- /eqP <-.
      by case => <- <-; rewrite !eqxx.
    apply (@equivP ((e1 == e2) /\ (l1 == l2)));first by apply andP.
    by split => [ [] /eqP -> /eqP -> //| [] -> ->];rewrite !eqxx.
  Qed.

  Definition linstr_r_eqMixin := Equality.Mixin eqb_r_axiom.

  Definition eqb i1 i2 :=
    (li_ii i1 == li_ii i2) && (eqb_r (li_i i1) (li_i i2)).

  Lemma eqb_axiom : Equality.axiom eqb.
  Proof.
    case=> [ii1 i1] [ii2 i2];rewrite /eqb /=.
    apply (@equivP ((ii1 == ii2) /\ eqb_r i1 i2));first by apply andP.
    split => [[]/eqP -> /eqb_r_axiom -> // | [] -> ->];rewrite eqxx;split => //.
    by apply /eqb_r_axiom.
  Qed.

  Definition linstr_eqMixin := Equality.Mixin eqb_axiom.

  Module Exports.
  Canonical linstr_r_eqType  := Eval hnf in EqType linstr_r linstr_r_eqMixin.
  Canonical linstr_eqType  := Eval hnf in EqType linstr linstr_eqMixin.
  End Exports.
End Eq_linstr.
Export Eq_linstr.Exports.
