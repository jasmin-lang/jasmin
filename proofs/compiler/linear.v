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

Require Import expr compiler_util.
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
 lfd_stk_size : Z;
 lfd_tyin : seq stype;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_tyout : seq stype;
 lfd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
 lfd_to_save: seq (var * Z);
 lfd_save_stack: saved_stack;
 lfd_export: bool;
}.

Definition signature_of_lfundef (lfd: lfundef) : function_signature :=
  (lfd_tyin lfd, lfd_tyout lfd).

Record lprog :=
 {  lp_rip   : Ident.ident;
    lp_globs : seq u8;
    lp_stk_id: Ident.ident;
    lp_funcs : seq (funname * lfundef) }.




(* --------------------------------------------------------------------------- *)
(* Uniq vmap                                                                   *)

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

  Context (writefun: funname -> Sv.t).
  
  Section CHECK_c.

    Context (check_i: instr -> Sv.t -> ciexec Sv.t).

    Fixpoint check_c (c:cmd) (s:Sv.t) := 
      match c with
      | [::] => ok s
      | i::c => 
        Let s := check_c c s in
        check_i i s
      end.

    Context (ii:instr_info) (c1:cmd) (e:pexpr) (c2:cmd).

    Fixpoint wloop (n:nat) (s: Sv.t) := 
      match n with
      | 0 => cierror ii (Cerr_Loop "linear check")
      | S n =>
        (* while c1 e c2 = c1; while e do c2; c1 *)
        let se := read_e_rec s e in
        Let s1 := check_c c1 se in
        Let s2 := check_c c2 s1 in
        if Sv.subset s2 s then ok s1
        else wloop n (Sv.union s2 s)
      end.

  End CHECK_c.

  Section CHECK_i.
 
  Context (stack_align : wsize).
 
  Fixpoint check_i (i:instr) (D:Sv.t) := 
    let (ii,ir) := i in
    match ir with
    | Cassgn x tag ty e => 
      if ty is sword sz then
        ok (read_rv_rec (read_e_rec (Sv.diff D (vrv x)) e) x)
      else cierror ii (Cerr_linear "assign not a word")
    | Copn xs tag o es =>
      ok (read_es_rec (read_rvs_rec (Sv.diff D (vrvs xs)) xs) es)
    | Cif b c1 c2 =>
      Let D1 := check_c check_i c1 D in
      Let D2 := check_c check_i c2 D in
      ok (read_e_rec (Sv.union D1 D2) b)
    | Cfor _ _ _ => 
      cierror ii (Cerr_linear "for found in linear")
    | Cwhile _ c e c' =>
      if e == Pbool false then check_c check_i c D
      else wloop check_i ii c e c' Loop.nb D
    | Ccall _ xs fn es => 
      if get_fundef (p_funcs p) fn is Some fd then
        Let _ := assert (sf_align (f_extra fd) <= stack_align)%CMP
          (ii, Cerr_linear "caller need alignment greater than callee") in
        Let _ := assert (sf_return_address (f_extra fd) != RAnone)  
          (ii, Cerr_linear "nowhere to store the return address") in
        Let _ := assert (if sf_return_address (f_extra fd) is RAstack _ then extra_free_registers ii != None else true)
          (ii, Cerr_linear "no extra free register to compute the return address") in
        Let _ := assert 
          (all2 (λ e a, if e is Pvar (Gvar v _) then v_var v == v_var a else false) es (f_params fd))
          (ii, Cerr_linear "bad call args") in
        Let _ := assert 
          (all2 (λ x r, if x is Lvar v then v_var v == v_var r else false) xs (f_res fd))
          (ii, Cerr_linear "bad call dests") in
        let W := writefun_ra writefun fn in
        let D1 := read_rvs_rec (Sv.diff D (vrvs xs)) xs in (* Remark read_rvs xs is empty since all variables *)
        let inter := Sv.inter D1 W in
        Let _ := assert (Sv.is_empty inter) (ii, Cerr_needspill (Sv.elements inter)) in
        let D2 := read_es_rec D1 es in
        Let _ := assert (if extra_free_registers ii is Some r then negb (Sv.mem r D2) else true)
                        (ii, Cerr_linear "extra register for rastack is not free") in
        ok D2
      else cierror ii (Cerr_linear "call to unknown function")
    end.
 
  End CHECK_i.

  Definition check_fd (ffd:sfun_decl) := 
    let (fn,fd) := ffd in
    let saved_rsp := match fd.(f_extra).(sf_save_stack) with SavedStackNone | SavedStackStk _ => Sv.empty | SavedStackReg r => Sv.singleton r end in
    let O := read_es_rec saved_rsp (map Plvar fd.(f_res)) in
    let stack_align := fd.(f_extra).(sf_align) in
    Let I := add_finfo fn fn (check_c (check_i stack_align) fd.(f_body) O) in
    let e := fd.(f_extra) in
    Let _ := assert ((e.(sf_return_address) != RAnone) || (all (λ '(x, _), is_word_type x.(vtype) != None) e.(sf_to_save))) (Ferr_fun fn (Cerr_linear "bad to-save")) in
    match e.(sf_return_address) with
    | RAreg ra =>
      Let _ := assert (~~Sv.mem ra (writefun fn)) (Ferr_fun fn (Cerr_linear "the function writes its return address")) in
      assert(~~Sv.mem ra I)  (Ferr_fun fn (Cerr_linear "the function depends of its return address"))
    | RAnone | RAstack _ => ok tt
    end.

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

Let rsp : var := Var (sword Uptr) p.(p_extra).(sp_stk_id).
Let rspi : var_i := VarI rsp xH.
Let rspg : gvar := Gvar rspi Slocal.

Definition round_ws (ws:wsize) (sz: Z) : Z :=
  (let d := wsize_size ws in
   let (q,r) := Z.div_eucl sz d in
   if r == 0 then sz else (q + 1) * d)%Z.

(*TODO: use cast_const *)
Let cast_const sz := Papp1 (Oword_of_int Uptr) (Pconst sz).

Definition allocate_stack_frame (free: bool) (ii: instr_info) (sz: Z) : linstr :=
  let m i := {| li_ii := ii ; li_i := i |} in
  m (Lopn [:: Lvar rspi] (Ox86 (LEA Uptr))
          [:: Papp2 ((if free then Oadd else Osub) (Op_w Uptr))
              (Pvar rspg)
              (cast_const sz)
    ]).

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

  | Ccall _ xs fn es =>
    if get_fundef (p_funcs p) fn is Some fd then
      let e := f_extra fd in
      let ra := sf_return_address e in
      if ra == RAnone then (lbl, lc)
      else
        let sz := round_ws (sf_align e) (sf_stk_sz e) in
        let: (before, after) :=
           if sz == 0 then ([::], [::])
           else ([:: allocate_stack_frame false ii sz ], [:: allocate_stack_frame true ii sz ])
        in
        let lret := lbl in
        let lbl := next_lbl lbl in
        match sf_return_address e with
        | RAreg ra =>
          (lbl, before ++ MkLI ii (LstoreLabel (Lvar (VarI ra xH)) lret) :: MkLI ii (Lgoto (fn, xH)) :: MkLI ii (Llabel lret) :: after ++ lc)
        | RAstack z =>
          if extra_free_registers ii is Some ra
          then (lbl,
                before ++
                       MkLI ii (LstoreLabel (Lvar (VarI ra xH)) lret) ::
                       MkLI ii (Lopn [::Lmem Uptr rspi (cast_const z)] (Ox86 (MOV Uptr)) [:: Pvar {| gv := VarI ra xH ; gs := Slocal |} ]) ::
                       MkLI ii (Lgoto (fn, xH)) :: MkLI ii (Llabel lret) :: after ++ lc)
          else (lbl, lc)
        | RAnone => (lbl, lc)
        end
    else (lbl, lc )
  | Cfor _ _ _ => (lbl, lc)
  end.

Definition linear_fd (fd: sfundef) :=
  let e := fd.(f_extra) in
  let: (tail, head, lbl) :=
     match sf_return_address e with
     | RAreg r => ([:: MkLI xH (Ligoto (Pvar {| gv := VarI r xH ; gs := Slocal |})) ], [:: MkLI xH (Llabel 1) ], 2%positive)
     | RAstack z => ([:: MkLI xH (Ligoto (Pload Uptr rspi (cast_const z))) ], [:: MkLI xH (Llabel 1) ], 2%positive)
     | RAnone => ([::], [::], 1%positive)
     end
  in
  let fd' := linear_c linear_i (f_body fd) lbl tail in
  let is_export := sf_return_address e == RAnone in
  let res := if is_export then f_res fd else [::] in
  LFundef (sf_align e) (sf_stk_sz e) (f_tyin fd) (f_params fd) (head ++ fd'.2) (f_tyout fd) res (if is_export then sf_to_save e else [::]) (sf_save_stack e)
              is_export.

End FUN.

Definition linear_prog : cfexec lprog :=
  let wmap := mk_wmap in
  Let _ := assert (check_wmap wmap) (Ferr_msg (Cerr_linear "invalid wmap")) in 
  Let _ := check_prog (get_wmap wmap) in
  Let _ := assert (size p.(p_globs) == 0) 
             (Ferr_msg (Cerr_linear "invalid p_globs, please report")) in
  let funcs := map (fun '(f,fd) => (f, linear_fd f fd)) p.(p_funcs) in
  ok {| lp_rip   := p.(p_extra).(sp_rip);
        lp_globs := p.(p_extra).(sp_globs);
        lp_stk_id := p.(p_extra).(sp_stk_id);
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
