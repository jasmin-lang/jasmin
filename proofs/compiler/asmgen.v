Require Import low_memory x86_sem compiler_util.
Require Import x86_variables_proofs.
Import Utf8.
Import all_ssreflect.
Import oseq sem x86_variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(* Compilation of variables                                             *)
Variant destination :=
| DAddr of address
| DReg  of register
| DFlag of rflag.

Definition destination_beq (d d': destination) : bool :=
  match d, d' with
  | DAddr a, DAddr a' => a == a'
  | DReg r, DReg r' => r == r'
  | DFlag f, DFlag f' => f == f'
  | _, _ => false
  end.

Definition destination_eq_dec (d d': destination) : { d = d' } + { d ≠ d' }.
Proof.
  refine
  match
  (let b := destination_beq d d' in
  if b as b return { b = true } + { b = false } then left erefl else right erefl)
  with
  | left e => left _
  | right ne => right _
  end.
  abstract (case: d d' e => [ a | r | f ] [ a' | r' | f' ] //= /eqP; apply: f_equal).
  abstract (case: d d' ne => [ a | r | f ] [ a' | r' | f' ] //= /eqP ne k; refine (ne (let: erefl := k in erefl))).
Defined.

Definition destination_eqMixin := comparableClass destination_eq_dec.
Canonical destination_eqType := EqType _ destination_eqMixin.

(* -------------------------------------------------------------------- *)
Variant arg_ty := TYcondt | TYoprd | TYreg | TYireg | TYimm.

Scheme Equality for arg_ty.

Definition arg_ty_eqMixin := comparableClass arg_ty_eq_dec.
Canonical arg_ty_eqType := EqType arg_ty arg_ty_eqMixin.

Definition string_of_arg_ty (ty: arg_ty) : string :=
  match ty with
  | TYcondt => "TYcondt"
  | TYoprd => "TYoprd"
  | TYreg => "TYreg"
  | TYireg => "TYireg"
  | TYimm => "TYimm"
  end.

Definition interp_ty (ty : arg_ty) : Type :=
  match ty with
  | TYcondt => condt
  | TYoprd  => oprd
  | TYreg   => register
  | TYireg  => ireg
  | TYimm => word
  end.

Fixpoint interp_tys (tys : seq arg_ty) :=
  if tys is ty :: tys then
    interp_ty ty -> interp_tys tys
  else asm.

Fixpoint tys_t_rec (ty: Type) tys : Type :=
  match tys with
  | [::] => ty
  | ty' :: tys' => tys_t_rec (ty * interp_ty ty') tys'
  end.

Definition tys_tuple (tys: seq arg_ty) : Type :=
  match tys with
  | [::] => unit
  | ty :: tys => tys_t_rec (interp_ty ty) tys
  end.

Variant garg := Gcondt of condt | Goprd of oprd.

Definition garg_beq (g g': garg) : bool :=
  match g, g' with
  | Gcondt c, Gcondt c' => c == c'
  | Goprd o, Goprd o' => o == o'
  | _, _ => false
  end.

Definition garg_eq_dec (g g': garg) : { g = g' } + { g ≠ g' }.
Proof.
  refine
  match
  (let b := garg_beq g g' in
  if b as b return { b = true } + { b = false } then left erefl else right erefl)
  with
  | left e => left _
  | right ne => right _
  end.
  abstract (case: g g' e => [ c | o ] [ c' | o' ] //= /eqP; apply: f_equal).
  abstract (case: g g' ne => [ c | o ] [ c' | o' ] //= /eqP ne k; refine (ne (let: erefl := k in erefl))).
Defined.

Definition garg_eqMixin := comparableClass garg_eq_dec.
Canonical garg_eqType := EqType _ garg_eqMixin.

Definition string_of_garg (g: garg) : string :=
  match g with
  | Gcondt c => "Gcondt " ++ string_of_condt c
  | Goprd o => "Goprd " ++ string_of_oprd o
  end.

Definition typed_apply_garg_error {T} ii ty arg : ciexec T :=
  cierror ii (Cerr_assembler (AsmErr_string ("TAG " ++ string_of_garg arg ++ ": "++ string_of_arg_ty ty))).

Definition typed_apply_garg ii {T} (ty: arg_ty) (arg: garg) :
  (interp_ty ty → T) → ciexec T :=
    match ty, arg return (interp_ty ty → T) → ciexec T with
    | TYcondt, Gcondt c => λ op, ok (op c)
    | TYoprd, Goprd x => λ op, ok (op x)
    | TYreg, Goprd (Reg_op r) => λ op, ok (op r)
    | TYireg, Goprd (Reg_op r)=> λ op, ok (op (Reg_ir r))
    | TYireg, Goprd (Imm_op w)=> λ op, ok (op (Imm_ir w))
    | TYimm, Goprd (Imm_op w)=> λ op, ok (op w)
    | _, _ => λ _, typed_apply_garg_error ii ty arg
    end.

Definition typed_apply_gargs_error {T} ii : ciexec T :=
  cierror ii (Cerr_assembler (AsmErr_string "TAGs")).

Fixpoint typed_apply_gargs ii (tys: seq arg_ty) (iregs: seq garg)
  : interp_tys tys → ciexec asm :=
  match tys, iregs with
  | [::], [::] => @Ok _ _
  | ty :: tys', ir :: iregs' => λ op,
                          @typed_apply_garg ii _ ty ir op >>=
                           @typed_apply_gargs ii tys' iregs'
  | _, _ => λ _, typed_apply_gargs_error ii
  end.

(* -------------------------------------------------------------------- *)

(* Describe where to recover the argument in the intermediate language *)
Variant arg_desc :=
| ADImplicit of var
| ADExplicit of nat & option register.
 (* [ADExplicit i (Some x)] in this case the ith argument should be the register x (see SHL) *)

Definition arg_desc_beq ad1 ad2 :=
  match ad1, ad2 with
  | ADImplicit x1, ADImplicit x2 => x1 == x2
  | ADExplicit i1 ox1, ADExplicit i2 ox2 => (i1 == i2) && (ox1 == ox2)
  | _, _ => false
  end.

Lemma arg_desc_beq_axiom : Equality.axiom arg_desc_beq.
Proof.
  move=> [x1 | i1 ox1] [x2 | i2 ox2] //=.
  + by case: (x1 =P x2) => [-> | neq ];constructor;congruence.
  + by constructor.
  + by constructor.
  case: (i1 =P i2) => [-> | neq ];last by constructor;congruence.
  by case: (_ =P _) => [-> | neq ];constructor;congruence.
Qed.

Definition arg_desc_eqMixin := Equality.Mixin arg_desc_beq_axiom .
Canonical arg_desc_eqType := EqType _ arg_desc_eqMixin.

Definition wf_implicit (ad: arg_desc) : bool :=
  if ad is ADImplicit x then
    compile_var x != None
  else true.

(* -------------------------------------------------------------------- *)
(* Generated ASM semantics                                              *)

Variant argument :=
 | Aflag  of rflag
 | Aoprd  of oprd
 | Acondt of condt.

Definition argument_beq (a a': argument) : bool :=
  match a, a' with
  | Aflag f, Aflag f' => f == f'
  | Aoprd o, Aoprd o' => o == o'
  | Acondt c, Acondt c' => c == c'
  | _, _ => false
  end.

Lemma argument_beq_axiom : Equality.axiom argument_beq.
Proof.
case => [ f | o | c ] [ f' | o' | c' ] /=;
  try (right; refine (λ e, let 'erefl := e in I));
  case: eqP => [ -> | ne ]; constructor => // k; refine (ne (let 'erefl := k in erefl)).
Qed.

Definition argument_eqMixin := Equality.Mixin argument_beq_axiom .
Canonical argument_eqType := EqType _ argument_eqMixin.

Definition arg_of_reg_or_flag (d: register + rflag): argument :=
  match d with
  | inl r => Aoprd (Reg_op r)
  | inr f => Aflag f
  end.

Definition arg_of_garg (i: garg) : argument :=
  match i with
  | Gcondt c => Acondt c
  | Goprd o => Aoprd o
  end.

Definition low_sem_ad_in (xs : seq garg) (ad : arg_desc) : option argument :=
  match ad with
  | ADImplicit x => ssrfun.omap arg_of_reg_or_flag (compile_var x)
  | ADExplicit n None => ssrfun.omap arg_of_garg (onth xs n)
  | ADExplicit n (Some x) =>
    let r1 := ssrfun.omap arg_of_garg (onth xs n) in
    let r2 := Some (Aoprd (Reg_op x)) in
    if r1 == r2 then r1 else None
  end.

Definition dest_of_reg_or_flag (d: register + rflag): destination :=
  match d with
  | inl r => DReg r
  | inr f => DFlag f
  end.

Definition low_sem_ad_out (xs : seq garg) (ad : arg_desc) : option destination :=
  match ad with
  | ADImplicit x => ssrfun.omap dest_of_reg_or_flag (compile_var x)
  | ADExplicit n None =>
    onth xs n >>= λ g,
    match g with
    | Goprd (Reg_op r) => Some (DReg r)
    | Goprd (Adr_op a) => Some (DAddr a)
    | _ => None
    end
  | _ => None
  end%O.

(*
Definition st_get_rflag_lax (f: rflag) (m: x86_mem) : value :=
  if m.(xrf) f is Def b then Vbool b else Vundef sbool.
*)

Definition eval_low gd (m : x86_mem) (a : argument) : exec value :=
  match a with
  | Aflag f => value_of_bool (st_get_rflag f m)
  | Aoprd o => read_oprd gd o m >>= λ w, ok (Vword w)
  | Acondt c => value_of_bool (eval_cond c m.(xrf))
  end.

Definition set_low (d: destination) (v: value) (m: x86_mem) : result _ x86_mem :=
  match d, v with
  | DAddr a, Vword w =>
    let x := decode_addr m a in
    mem_write_mem x w m
  | DReg r, Vword w => ok (mem_write_reg r w m)
  | DFlag f, Vbool b => ok (mem_set_rflags f b m)
  | DFlag f, Vundef sbool => ok (mem_unset_rflags f m)
  | _, _ => type_error
  end.

Definition sets_low (m : x86_mem) (x : seq destination) (v : seq value) :=
  if size x == size v then
    foldl (fun m xv => Result.bind (set_low xv.1 xv.2) m) (ok m) (zip x v)
  else type_error.

Definition low_sem_aux (gd: glob_defs) (m: x86_mem) (op: sopn)
           (outx inx: seq arg_desc) (xs: seq garg) : exec x86_mem :=
  let inx := oseq.omap (low_sem_ad_in xs) inx in
  let outx := oseq.omap (low_sem_ad_out xs) outx in
  if (inx, outx) is (Some inx, Some outx) then
    mapM (eval_low gd m) inx >>= exec_sopn op >>= sets_low m outx
  else type_error.

(* -------------------------------------------------------------------- *)
Definition mk_garg ty : interp_ty ty -> garg :=
  match ty with
  | TYcondt => Gcondt
  | TYoprd => Goprd
  | TYreg  => fun r => Goprd (Reg_op r)
  | TYireg => fun ir => Goprd (match ir with Imm_ir i => Imm_op i | Reg_ir r => Reg_op r end)
  | TYimm => fun i => Goprd (Imm_op i)
  end.

Fixpoint seq_of_tys_t_rec ty tys : (ty -> list garg) -> tys_t_rec ty tys -> list garg :=
  match tys with
  | [::] => fun k t => k t
  | ty'::tys => fun k => @seq_of_tys_t_rec (ty * interp_ty ty')%type tys
     (fun (p:ty * interp_ty ty') => rcons (k p.1) (@mk_garg ty' p.2))
  end.

Definition seq_of_tys_tuple tys : tys_tuple tys -> list garg :=
  match tys with
  | [::] => fun tt => [::]
  | ty::tys => @seq_of_tys_t_rec (interp_ty ty) tys (fun a => [::@mk_garg ty a])
  end.

Definition is_sopn (i: asm) : bool :=
  match i with
  | LABEL _ | JMP _ | Jcc _ _ => false
  | _ => true
  end.

Fixpoint gen_sem_correct tys id_name id_out id_in args  : interp_tys tys -> Prop :=
  match tys with
  | [::] => fun asm =>
    is_sopn asm ∧
    ∀ gd m m',
       low_sem_aux gd m id_name id_out id_in args = ok m' →
       eval_instr_mem gd asm m = ok m'
  | ty::tys => fun asm =>
    forall (x:interp_ty ty), @gen_sem_correct tys id_name id_out id_in (args ++ [::@mk_garg ty x]) (asm x)
  end.

Arguments gen_sem_correct : clear implicits.

Record instr_desc := mk_instr_desc {
  id_name : sopn;
  id_out  : seq arg_desc;
  id_in   : seq arg_desc;
  id_tys  : seq arg_ty;
  id_instr: interp_tys id_tys;

  (* FIXME : Add the functionnal semantic of the operator in the record,
             this require to the have its syntatic type *)
  id_gen_sem : gen_sem_correct id_tys id_name id_out id_in [::] id_instr;
  id_in_wf   : all wf_implicit id_in;
  id_out_wf  : all wf_implicit id_out;
}.

Definition low_sem gd m (id: instr_desc) (gargs: seq garg) : x86_result :=
  low_sem_aux gd m id.(id_name) id.(id_out) id.(id_in) gargs.

(* -------------------------------------------------------------------- *)
(* Generated mixed semantics                                            *)

Definition is_var (x:var) e :=
  match e with
  | Pvar x' => x == x'
  | _ => false
  end.

Definition mixed_sem_ad_in (xs : seq pexpr) (ad : arg_desc) : option pexpr :=
  match ad with
  | ADImplicit x => Some (Pvar (VarI x xH))
  | ADExplicit n None => onth xs n
  | ADExplicit n (Some x) =>
    onth xs n >>= fun e => if is_var (var_of_register x) e then Some e else None
  end%O.

Definition lval_of_pexpr e :=
  match e with
  | Pvar v    =>
    if vtype v == sbool then None else Some (Lvar v)
  | Pload x e => Some (Lmem x e)
  | _         => None
  end.

Definition mixed_sem_ad_out (xs : seq pexpr) (ad : arg_desc) : option lval :=
  match ad with
  | ADImplicit x => Some (Lvar (VarI x xH))
  | ADExplicit n None =>
    onth xs n >>= lval_of_pexpr
  | _ => None
  end%O.

Definition mixed_sem gd m (id : instr_desc) (xs : seq pexpr) :=
  let: inx  := oseq.omap (mixed_sem_ad_in xs) id.(id_in ) in
  let: outx := oseq.omap (mixed_sem_ad_out xs) id.(id_out) in
  if (inx, outx) is (Some inx, Some outx) then
    sem_sopn gd id.(id_name) m outx inx
  else type_error.

(* -------------------------------------------------------------------- *)
(* High level to mixed semantics                                        *)

Definition check_sopn_arg (loargs : seq pexpr) (x : pexpr) (ad : arg_desc) :=
  match ad with
  | ADImplicit y => is_var y x
  | ADExplicit n o =>
    (n < size loargs) && (x == nth x loargs n) &&
    match o with
    | None => true
    | Some y => is_var (var_of_register y) x
    end
  end.

Definition is_lvar (x:var) lv :=
  match lv with
  | Lvar y => x == y
  | _ => false
  end.

Definition check_sopn_res (loargs : seq pexpr) (x : lval) (ad : arg_desc) :=
  match ad with
  | ADImplicit y => is_lvar y x
  | ADExplicit n (Some _) => false
  | ADExplicit n None =>
    if (onth loargs n >>= lval_of_pexpr)%O is Some y
    then eq_lval x y
    else false
  end.

Lemma is_varP x e : is_var x e ->  eq_expr e {| v_var := x; v_info := xH |}.
Proof. by case e => //= v /eqP ->. Qed.

Lemma check_sopn_argP (loargs hiargs : seq pexpr) (ads : seq arg_desc) :
     all2 (check_sopn_arg loargs) hiargs ads →
     ∃ hiargs',
       oseq.omap (mixed_sem_ad_in loargs) ads = Some hiargs'
       ∧ all2 eq_expr hiargs hiargs'.
Proof.
  elim: hiargs ads => [ | e hiargs Hrec] [ | a ads] //=.
  + by move=> _;exists nil.
  move=> /andP [Hc /Hrec [hiargs' [-> Hall]]] /=.
  rewrite /mixed_sem_ad_in; case: a Hc => //=.
  + by move=> y /is_varP Hy;eexists;split;[by eauto | ];rewrite /= Hy.
  move=> n o /andP [] /andP [] Hlt /eqP -> Ho.
  exists  (nth e loargs n :: hiargs').
  rewrite (onth_nth_size e Hlt) /= Hall andbT;split;last by apply eq_expr_refl.
  by case: o Ho => // y ->.
Qed.

Lemma is_lvarP x e : is_lvar x e ->  eq_lval e {| v_var := x; v_info := xH |}.
Proof. by case e => //= v /eqP ->. Qed.

Lemma check_sopn_resP (loargs : seq pexpr) (lval : seq lval) (ads : seq arg_desc) :
     all2 (check_sopn_res loargs) lval ads →
     ∃ lval',
       oseq.omap (mixed_sem_ad_out loargs) ads = Some lval'
       ∧ all2 eq_lval lval lval'.
Proof.
  elim: lval ads => [ | lv lval Hrec] [ | a ads] //=.
  + by move=> _; exists nil.
  move=> /andP [Hc /Hrec [lval' [-> Hall]]] /=.
  rewrite /mixed_sem_ad_out; case: a Hc => //=.
  + by move=> y /is_lvarP Hy;eexists;split;[by eauto | ];rewrite /= Hy.
  move => n [] //; case: (_ >>= _)%O => // lv' h; eexists; split; first by eauto.
  by rewrite /= h.
Qed.

Definition check_sopn_args ii
  (id: instr_desc) (outx : seq lval) (inx : seq pexpr) (loargs : seq pexpr) : ciexec unit :=
  if all2 (check_sopn_res loargs) outx id.(id_out)
  then
  if all2 (check_sopn_arg loargs) inx  id.(id_in )
  then ok tt
  else cierror ii (Cerr_assembler (AsmErr_string "check_sopn_arg"))
  else cierror ii (Cerr_assembler (AsmErr_string "check_sopn_res")).

Theorem check_sopnP ii gd o descr outx inx loargs m1 m2 :
  id_name descr = o →
  check_sopn_args ii descr outx inx loargs = ok tt
  -> sem_sopn gd o m1 outx inx = ok m2
  -> mixed_sem gd m1 descr loargs = ok m2.
Proof.
  rewrite /check_sopn_args => Hdesc.
  case: ifP => // h1; case: ifP => // h2 _.
  rewrite /mixed_sem /sem_sopn.
  have [inx' [-> /eq_exprsP ->]] := check_sopn_argP h2.
  have [outx' [-> /eq_lvalsP H]]:= check_sopn_resP h1.
  rewrite Hdesc.
  by t_xrbindP => vs ws -> /= ->;rewrite H.
Qed.

(* ----------------------------------------------------------------------------- *)
Variant source_position :=
  | InArgs of nat
  | InRes  of nat.

Definition pexpr_of_lval ii (lv:lval) : ciexec pexpr :=
  match lv with
  | Lvar x    => ok (Pvar x)
  | Lmem x e  => ok (Pload x e)
  | Lnone _ _
  | Laset _ _ => cierror ii (Cerr_assembler (AsmErr_string "pexpr_of_lval"))
  end.

Definition get_loarg ii (outx: seq lval) (inx:seq pexpr) (d:source_position) : ciexec pexpr :=
  let o2e {A} (m: option A) :=
      match m with
      | Some pe => ok pe
      | None => cierror ii (Cerr_assembler (AsmErr_string "get_loarg"))
      end in
  match d with
  | InArgs x => o2e (onth inx x)
  | InRes  x => o2e (onth outx x) >>= pexpr_of_lval ii
  end.

Definition nmap (T:Type) := nat -> option T.
Definition nget (T:Type) (m:nmap T) (n:nat) := m n.
Definition nset (T:Type) (m:nmap T) (n:nat) (t:T) :=
  fun x => if x == n then Some t else nget m x.
Definition nempty (T:Type) := fun n:nat => @None T.

Definition set_expr (m:nmap source_position) (n:nat) (x:source_position) :=
  match nget m n with
  | Some _ => m
  | None   => nset m n x
  end.

Definition compile_hi_arg (p:nat -> source_position) (ad: arg_desc) (i:nat) (m: nmap source_position) :=
  match ad with
  | ADImplicit _ => m
  | ADExplicit n _ => set_expr m n (p i)
  end.

Definition mk_loargs id : seq source_position :=
  let m := foldl (fun m p => compile_hi_arg InArgs p.1 p.2 m) (nempty _)
                 (zip id.(id_in) (iota 0 (size id.(id_in)))) in
  let m := foldl (fun m p => compile_hi_arg InRes p.1 p.2 m) m
                 (zip id.(id_out) (iota 0 (size id.(id_out)))) in
  odflt [::] (oseq.omap (nget m) (iota 0 (size id.(id_tys)))).

Definition compile_hi_sopn ii (id: instr_desc) (outx : lvals) (inx : pexprs) : ciexec pexprs :=
  mapM (get_loarg ii outx inx) (mk_loargs id) >>= λ loargs,
  check_sopn_args ii id outx inx loargs >>= λ _,
  ok loargs.

Lemma compile_hiP ii (id: instr_desc) (outx : lvals) (inx : pexprs) loargs :
  compile_hi_sopn ii id outx inx = ok loargs →
  check_sopn_args ii id outx inx loargs = ok tt.
Proof.
by rewrite /compile_hi_sopn; t_xrbindP => ? _ [] ? <-.
Qed.

Theorem compile_hi_sopnP ii gd op descr outx inx m1 m2 loargs :
  id_name descr = op →
  compile_hi_sopn ii descr outx inx = ok loargs →
  sem_sopn gd op m1 outx inx = ok m2 →
  mixed_sem gd m1 descr loargs = ok m2.
Proof.
by move => h /compile_hiP /(check_sopnP h); apply.
Qed.

(* -------------------------------------------------------------------- *)
(* Mixed semantics to generated ASM semantics                           *)

Definition compile_pexpr ii (ty_arg: arg_ty * pexpr) : ciexec garg :=
  let: (ty, arg) := ty_arg in
  if ty == TYcondt then
    assemble_cond ii arg >>= λ c, ok (Gcondt c)
  else
    oprd_of_pexpr ii arg >>= λ o, ok (Goprd o)
.

Lemma compile_pexpr_eq_expr ii ty pe pe' r :
  eq_expr pe pe' →
  compile_pexpr ii (ty, pe) = ok r →
  compile_pexpr ii (ty, pe) = compile_pexpr ii (ty, pe').
Proof.
  move => h; rewrite /compile_pexpr.
  case: eqP => _; t_xrbindP => z hz ?; subst r.
  + by rewrite (assemble_cond_eq_expr h hz).
  by rewrite (oprd_of_pexpr_eq_expr h hz).
Qed.

Definition compile_low_args ii (tys: seq arg_ty) (args: pexprs) : ciexec (seq garg) :=
  if size tys == size args then
    mapM (compile_pexpr ii) (zip tys args)
  else cierror ii (Cerr_assembler (AsmErr_string "compile_low_args")).

Definition any_ty : arg_ty := TYimm.
Definition any_garg : garg := Goprd (Imm_op I64.zero).
Definition any_pexpr : pexpr := 0%Z.
Definition any_ty_pexpr : arg_ty * pexpr := (any_ty, any_pexpr).

Lemma compile_low_argsP ii tys pes gargs :
  compile_low_args ii tys pes = ok gargs →
  size tys = size pes ∧ mapM (compile_pexpr ii) (zip tys pes) = ok gargs.
Proof. by rewrite/compile_low_args; case: eqP. Qed.

Lemma compile_low_eval ii gd ty m lom pe g v :
  lom_eqv m lom →
  sem_pexpr gd m pe = ok v →
  compile_pexpr ii (ty, pe) = ok g →
  ∃ v',
    eval_low gd lom (arg_of_garg g) = ok v' ∧
    value_uincl v v'.
Proof.
rewrite /compile_pexpr => eqm hv.
case: eqP => hty; t_xrbindP => x hx ?; subst g => /=.
- case: eqm => _ _ eqf.
  by have /(_ gd _ hv) := eval_assemble_cond eqf hx.
have [w -> hvw] := eval_oprd_of_pexpr eqm hx hv.
by exists w.
Qed.

Lemma compile_low_args_in ii gd m lom ads tys pes args gargs :
  lom_eqv m lom →
  compile_low_args ii tys pes = ok gargs →
  all wf_implicit ads →
  oseq.omap (mixed_sem_ad_in pes) ads = Some args →
  ∃ loargs,
    oseq.omap (low_sem_ad_in gargs) ads = Some loargs ∧
    ∀ vs,
    mapM (sem_pexpr gd m) args = ok vs →
    ∃ vs',
    mapM (eval_low gd lom) loargs = ok vs' ∧
    List.Forall2 value_uincl vs vs'.
Proof.
  move => eqm hpes.
  elim: ads args.
  - by  move => args _ [] <-; exists [::]; split => // ? [] <-; exists [::].
  move => ad ads ih args' h; rewrite /= in h; case/andP: h => hwf hwf'.
  case/omap_consI => arg [] args [] -> ha has.
  case: (ih _ hwf' has) => {ih} loargs [hlo hlo'].
  case: ad ha hwf.
  (* Implicit *)
  + move => x /= [] ?; subst arg.
    case hd: compile_var => [ d | ] //= _.
    exists (arg_of_reg_or_flag d :: loargs); split; first by rewrite /= hlo.
    t_xrbindP => vs' v hv vs ok_vs <- {vs'}.
    have [vs1 [hvs1 hvsvs1]] := hlo' _ ok_vs.
    case: eqm => hm hr hf.
    move: hd; rewrite/compile_var.
    case eq1: register_of_var => [ r | ].
    * have := var_of_register_of_var eq1 => {eq1} ?; subst x.
      case => <- /=.
      exists (Vword (xreg lom r) :: vs1); split.
      + by rewrite hvs1.
      constructor => //. exact: hr.
    case eq2: flag_of_var => [ f | ] // [<-] {d}.
    have := var_of_flag_of_var eq2 => {eq1 eq2} ?; subst x.
    exists (of_rbool (xrf lom f) :: vs1); split.
    + have := hf _ _ hv.
      by rewrite /= /st_get_rflag hvs1; case: (xrf lom f).
    constructor => //. exact: hf.
  (* Explicit *)
  case/compile_low_argsP: hpes => hsz hpes.
  move => /= n o ho _.
  have : onth pes n = Some arg ∧ match o with Some x => eq_expr arg {| v_var := var_of_register x ; v_info := xH |} | _ => true end.
  + by case: o ho => // x /obindI [] e [] ->; case: ifP => // /is_varP h [] ?; subst.
  case => /onthP - /(_ any_pexpr) /andP [] hn /eqP ? {ho} ho; subst arg.
  have hna : n < size gargs by rewrite - (mapM_size hpes) size_zip hsz minnn.
  rewrite (onth_nth_size any_garg hna) /=.
  have := mapM_nth any_ty_pexpr any_garg hpes.
  rewrite size_zip hsz minnn => /(_ _ hn).
  rewrite nth_zip => //.
  set z := nth any_garg gargs n.
  set pe := nth any_pexpr pes n.
  move => hnth.
  set y := match o with Some _ => _ | _ => _ end.
  have : y = Some (arg_of_garg z).
  + subst y. case: o ho => // v hv.
    move: (hnth).
    rewrite (compile_pexpr_eq_expr hv hnth) {hv}.
    rewrite /compile_pexpr. case: eqP => // _; t_xrbindP => op.
    by rewrite /= reg_of_stringK => -[ <-] <- /=; rewrite eqxx.
  move -> => {y}.
  rewrite hlo /=. eexists; split; first by eauto.
  t_xrbindP => vs' v ok_v vs ok_vs <- {vs'} /=.
  have [vs' [ok_vs' hvsvs']] := hlo' _ ok_vs.
  rewrite ok_vs' /=.
  have [v' [ok_v' hvv']] := compile_low_eval eqm ok_v hnth.
  exists (v' :: vs'); split.
  + by rewrite ok_v'.
  by constructor.
Qed.

Lemma write_var_compile_var x y y0 m lom m1 rf :
  write_var x y m = ok m1 →
  value_uincl y y0 →
  lom_eqv m lom →
  compile_var x = Some rf →
  exists2 lom1, set_low (dest_of_reg_or_flag rf) y0 lom = ok lom1 & lom_eqv m1 lom1.
Proof.
rewrite /write_var /compile_var.
case: x => -[ty x] /= _.
t_xrbindP => vm hwv <- {m1} hvu eqm.
case: register_of_var (@var_of_register_of_var (Var ty x)) => [ r | ].
- (* Register *)
  move => /(_ _ erefl) [? ?]; subst x ty .
  case => <- /= {rf}.
  move: hwv. apply: set_varP => //= w ok_w <- {vm}.
  have [? ?] := value_uincl_word hvu ok_w.
  subst y y0 => {hvu ok_w}.
  eexists; first by reflexivity.
  case: eqm => eqm eqr eqf.
  split => //=.
  + move => r' v; apply: on_vuP.
    * move => /= w' hw' <- {v}; move: hw'.
      rewrite ffunE; case: eqP.
      - by move => ?; subst r'; rewrite Fv.setP_eq => -[<-].
      move => ne ; rewrite Fv.setP_neq.
      - by move => hw'; apply: eqr; rewrite /get_var hw'.
      by apply/eqP => -[] k; have ?:= inj_string_of_register k; apply: ne.
    by move => _ [<-].
  move => f v /= h; apply: eqf; move: h.
  rewrite /get_var; apply: on_vuP.
  + by move => /= b h <- {v}; move: h; rewrite Fv.setP_neq => // ->.
  by rewrite Fv.setP_neq => //= ->.
(* Flag *)
move => _.
case: flag_of_var (@var_of_flag_of_var (Var ty x)) => [ f | // ].
move => /(_ _ erefl) [? ?] [<-] /= {rf}; subst ty x.
move: hwv. apply: set_varP => /=.
- (* Set *)
  move => b; case: y hvu => // [ | [] //] /= b'; case: y0 => // c <- {c} [->] {b'} <-.
  eexists; first by reflexivity.
  case: eqm => eqm eqr eqf.
  split => //=.
  + move => r' v; apply: on_vuP.
    * move => /= w' hw' <- {v}; move: hw'.
      rewrite Fv.setP_neq => // h.
      by have := eqr r' w'; rewrite /get_var /= h => /(_ erefl).
    by move => _ [<-].
  move => f' v /=; rewrite /get_var /=; apply: on_vuP.
  + move => b' hb' <- {v}; move: hb'.
    rewrite ffunE; case: eqP.
    - by move => ?; subst f'; rewrite Fv.setP_eq => -[<-].
    move => ne ; rewrite Fv.setP_neq.
    - by move => hw'; apply: eqf; rewrite /get_var hw'.
    by apply/eqP => -[] k; have ?:= inj_string_of_rflag k; apply: ne.
  by move => _ [<-] /=; case: ((RflagMap.set _ _ _) f').
(* Unset *)
move => _; case: y hvu => // -[] // hvu _ <- {vm}.
case: eqm => eqm eqr eqf.
case: y0 hvu => // [ b | [] //] _; (eexists; first by reflexivity); split => //=.
  + move => r' v; apply: on_vuP.
    * move => /= w' hw' <- {v}; move: hw'.
      rewrite Fv.setP_neq => // h.
      by have := eqr r' w'; rewrite /get_var /= h => /(_ erefl).
    by move => _ [<-].
  move => f' v /=; rewrite /get_var /=; apply: on_vuP.
  + move => b' hb' <- {v}; move: hb'.
    rewrite ffunE; case: eqP.
    - by move => ?; subst f'; rewrite Fv.setP_eq.
    move => ne ; rewrite Fv.setP_neq.
    - by move => hw'; apply: eqf; rewrite /get_var hw'.
    by apply/eqP => -[] k; have ?:= inj_string_of_rflag k; apply: ne.
  by move => _ [<-] /=; case: ((RflagMap.set _ _ _) f').
  + move => r' v; apply: on_vuP.
    * move => /= w' hw' <- {v}; move: hw'.
      rewrite Fv.setP_neq => // h.
      by have := eqr r' w'; rewrite /get_var /= h => /(_ erefl).
    by move => _ [<-].
  move => f' v /=; rewrite /get_var /=; apply: on_vuP.
  + move => b' hb' <- {v}; move: hb'.
    rewrite ffunE; case: eqP.
    - by move => ?; subst f'; rewrite Fv.setP_eq.
    move => ne ; rewrite Fv.setP_neq.
    - by move => hw'; apply: eqf; rewrite /get_var hw'.
    by apply/eqP => -[] k; have ?:= inj_string_of_rflag k; apply: ne.
  by move => _ [<-] /=; case: ((RflagMap.oset _ _ _) f').
Qed.

Lemma compile_lval_of_pexpr ii ty pe g lv :
  compile_pexpr ii (ty, pe) = ok g →
  lval_of_pexpr pe = Some lv →
  ∃ ra : register + address,
  g = Goprd match ra with inl r => Reg_op r | inr a => Adr_op a end
  ∧ match ra with
    | inl r =>
      ∃ x, pe = Pvar x ∧ lv = Lvar x ∧ register_of_var x = Some r
    | inr a => ∃ x ofs d,
  pe = Pload x ofs ∧ lv = Lmem x ofs ∧ register_of_var x = Some d ∧ addr_of_pexpr ii d ofs = ok a
end.
Proof.
rewrite /compile_pexpr; case: eqP => hty; t_xrbindP => r hr <- {g}.
- by case: pe hr => //=; case => -[] [].
case: pe hr => //=.
- case => -[] [] //= x xi; t_xrbindP => f ok_f [<-] {r} [<-] {lv}; exists (inl f); split => //.
  eexists; do 2 (split => //).
  rewrite /register_of_var /=.
  by case: reg_of_string ok_f => // ? [->].
t_xrbindP => x pe d ok_d a ok_a [<-] {r} [<-] {lv}; exists (inr a); split => //.
exists x, pe, d; repeat (split => //).
case: x ok_d => -[] [] // x xi.
rewrite /register_of_var /=.
by case: reg_of_string => // ? [->].
Qed.

Lemma compile_low_args_out ii gd ads tys pes args gargs :
  compile_low_args ii tys pes = ok gargs →
  all wf_implicit ads →
  oseq.omap (mixed_sem_ad_out pes) ads = Some args →
  ∃ loargs,
    oseq.omap (low_sem_ad_out gargs) ads = Some loargs ∧
    ∀ ys m m' ys' lom,
    lom_eqv m lom →
    write_lvals gd m args ys = ok m' →
    List.Forall2 value_uincl ys ys' →
    ∃ lom',
    sets_low lom loargs ys' = ok lom' ∧
    lom_eqv m' lom'.
Proof.
  move => hpes.
  elim: ads args => [ | ds ads ih] args /=.
  + move=> _ [<-];exists [::];split=>// -[ | //] ??? lom eqm [<-] /List_Forall2_inv_l ->.
    by exists lom.
  move=> /andP [wds wads]. case Heq: mixed_sem_ad_out => [lv | //].
  case Heq' : omap => [ lvs /=| //] [<-].
  have [loargs [-> H]]:= ih _ wads Heq'.
  case: {ih} ds Heq wds => /=.
  + move=> v [<-]; case Heq1: compile_var => [rf | //] _ /=.
    eexists;split;first by eauto.
    move=> [ // | y ys] m m' ys'' lom eqm.
    t_xrbindP => m1 Hwr Hwv /List_Forall2_inv_l [y'] [ys'] [->] {ys''} [hyy' hysys'].
    have [lom1 /= Hset eqm1]:= write_var_compile_var Hwr hyy' eqm Heq1.
    have [lom' []]:= H _ _ _ _ _ eqm1 Hwv hysys'.
    by rewrite /sets_low;case:ifP => //= /eqP ->;rewrite eqxx Hset => ->;eauto.
  case/compile_low_argsP: hpes => hsz hpes.
  move => n [ ? // | ] /obindI [pe] [hpe hlv] _.
  move: hpe => /onthP - /(_ any_pexpr) /andP [] hn /eqP ?; subst pe.
  have hna : n < size gargs by rewrite - (mapM_size hpes) size_zip hsz minnn.
  rewrite (onth_nth_size any_garg hna) /=.
  have := mapM_nth any_ty_pexpr any_garg hpes.
  rewrite size_zip hsz minnn => /(_ _ hn).
  rewrite nth_zip => //.
  set z := nth any_garg gargs n.
  set pe := nth any_pexpr pes n.
  set ty := nth any_ty tys n.
  move => hnth.
  rewrite -/pe in hlv.
  have [ra [hz hra]] := compile_lval_of_pexpr hnth hlv => {hnth hlv}.
  rewrite hz.
  exists (match ra with inl r => DReg r | inr a => DAddr a end :: loargs); split.
  - by case: ra hz hra.
  move => [] // y ys m m'' ys'' lom eqm; t_xrbindP => m' ok_m' ok_m'' /List_Forall2_inv_l [y'] [ys'] [?] [hyy' hysys']; subst ys''.
  case: ra hz hra.
  - move => r hz [x] [hpe] [? hr]; subst lv.
    have := @write_var_compile_var _ _ _ _ _ _ (inl r) ok_m' hyy' eqm.
    rewrite /compile_var hr => /(_ erefl) /= [lom' ok_lom' eqm'].
    have [lom'' [ok_lom'' eqm'']] := H _ _ _ _ _ eqm' ok_m'' hysys'.
    exists lom''; split => //.
    by move: ok_lom''; rewrite /sets_low /=; case: ifP => // /eqP ->; rewrite eqxx ok_lom'.
  move => a hz [x] [ofs] [d] [hpe] [?] [hd ha]; subst lv.
  move: ok_m' => /=; t_xrbindP => v v' ok_v' ok_v w w' ok_w' ok_w u ok_u em ok_em ?; subst m'.
  set lom' := {| xmem := em ; xreg := xreg lom ; xrf := xrf lom |}.
  have eqm' : lom_eqv {| emem := em ; evm := evm m |} lom'.
  - by case: eqm => eqm eqr eqf; rewrite /lom'; split.
  have [lom'' [ok_lom'' eqm'']] := H _ _ _ _ _ eqm' ok_m'' hysys'.
  exists lom''; split => //.
  move: ok_lom''; rewrite /sets_low /=; case: ifP => // /eqP ->; rewrite eqxx.
  case: y ok_u hyy' => // [ y | [] // ] [?]; subst u; case: y' => // y' /= ?; subst y'.
  case: (eqm) => eqmem eqr eqf; rewrite /mem_write_mem -eqmem.
  suff : decode_addr lom a = (I64.add v w).
  - by rewrite /lom' => ->; rewrite ok_em.
  move: ha; rewrite /addr_of_pexpr /decode_addr.
  have hx := var_of_register_of_var hd. rewrite -hx in ok_v'.
  have := eqr _ _ ok_v'.
  case: v' ok_v ok_v' => // [ v' | [] // ] [->] {v'} ok_v /= ?; subst v.
  have := addr_ofsP ok_w' ok_w.
  clear -eqm.
  case: addr_ofs => //=.
  - move => z /(_ erefl) [<-] [<-] /=; rewrite !rw64; exact: I64.add_commut.
  - move => x /(_ erefl); t_xrbindP => v ok_v hvw r ok_r [<-] /=; rewrite !rw64.
    by have <- := xgetreg eqm ok_r ok_v hvw.
  - move => z x /(_ erefl); t_xrbindP => v v' ok_v' ok_v <- {w} r ok_r sc /xscale_ok ok_sc [<-] /=; rewrite !rw64 ok_sc.
    by have <- := xgetreg eqm ok_r ok_v' ok_v.
  move => z x z' /(_ erefl); t_xrbindP => v v' ok_v' ok_v <- {w} r ok_r sc /xscale_ok ok_sc [<-] /=; rewrite ok_sc.
  have <- := xgetreg eqm ok_r ok_v' ok_v.
  by rewrite I64.add_commut I64.add_assoc.
Qed.

Theorem mixed_to_low ii gd s s' id m pes gargs :
  lom_eqv s m →
  compile_low_args ii (id_tys id) pes = ok gargs →
  mixed_sem gd s id pes = ok s' →
  ∃ m',
    low_sem gd m id gargs = ok m'
    ∧ lom_eqv s' m'.
Proof.
  move => eqsm ok_args.
  rewrite /mixed_sem /sem_sopn.
  case ok_in: (omap _) => [ inx | // ].
  case ok_out: (omap _) => [ outx | // ].
  t_xrbindP => ys xs ok_xs ok_ys hs'.
  rewrite /low_sem /low_sem_aux.
  have [loin [-> /(_ _ ok_xs) [xs' [-> /= hxs]]]] := compile_low_args_in gd eqsm ok_args (id_in_wf id) ok_in.
  have [ys' [-> /= hys]] := vuincl_exec_opn hxs ok_ys.
  have [loout [-> ]]  := compile_low_args_out gd ok_args (id_out_wf id) ok_out.
  by move=> /(_ _ _ _ _ _ eqsm hs' hys).
 Qed.
