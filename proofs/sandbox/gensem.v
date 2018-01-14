(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import oseq.

Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope option_scope.

(* -------------------------------------------------------------------- *)
(* Syntax *)
Definition var := [countType of nat].
Parameter mem : Type.

Variant value :=
  | VInt  of int
  | VBool of bool.

Coercion VInt : int >-> value.
Coercion VBool : bool >-> value.

Variant expr := EVar of var | EInt of int.

Axiom expr_eqMixin : Equality.mixin_of expr.
Canonical expr_eqType := EqType _ expr_eqMixin.

Variant cmd_name := ADDC | SUBC | MUL.

Definition cmd : Type := cmd_name * seq var * seq expr.

(* -------------------------------------------------------------------- *)
(* Memory *)

Parameter get : mem -> var -> value.
Parameter set : mem -> var -> value -> mem.

Axiom get_set :
  ∀ m x v x',
    get (set m x v) x' = if x' == x then v else get m x'.

Definition sets (m : mem) (x : seq var) (v : seq value) :=
  if size x == size v then
    Some (foldl (fun m xv => set m xv.1 xv.2) m (zip x v))
  else None.

Lemma setsI m x v m' :
  sets m x v = Some m' →
  size x = size v ∧ m' = foldl (λ m xv, set m xv.1 xv.2) m (zip x v).
Proof.
  by rewrite/sets; case: eqP => // eqsz [].
Qed.

Lemma sets_consI m x xs v m' :
  sets m (x :: xs) v = Some m' →
  ∃ y ys, v = y :: ys ∧ sets (set m x y) xs ys = Some m'.
Proof.
  case/setsI; case: v => // y ys /= /succn_inj hsz ->.
  exists y, ys; split; first reflexivity.
  by rewrite /sets; case: eqP.
Qed.

(* -------------------------------------------------------------------- *)
(* Semantic high level *)

Definition eval (m : mem) (e : expr) :=
  match e return value with
  | EVar x => get m x
  | EInt i => i
  end.

Parameter addc : int * int * bool -> int * bool.
Parameter subc : int * int * bool -> int * bool.
Parameter mul : int * int -> int * int.

Definition sem_addc_val (args : seq value) :=
  if args is [:: VInt x; VInt y; VBool c] then
     let: (z, c) := addc (x, y, c) in Some [:: VInt z; VBool c]
  else None.

Definition sem_subc_val (args : seq value) :=
  if args is [:: VInt x; VInt y; VBool c] then
     let: (z, c) := subc (x, y, c) in Some [:: VInt z; VBool c]
  else None.

Definition sem_mul_val (args : seq value) :=
  if args is [:: VInt x; VInt y] then
     let: (z, c) := mul (x, y) in Some [:: VInt z; VInt c]
  else None.

Definition sem_cmd (op : seq value -> option (seq value)) m outv inv :=
  if op [seq eval m x | x <- inv] is Some res then
    sets m outv res
  else None.

Definition semop (c : cmd_name) := 
  match c with
  | ADDC => sem_addc_val
  | SUBC => sem_subc_val
  | MUL => sem_mul_val
  end.

Definition semc (m : mem) (c : cmd) : option mem :=
  let: (c, outv, inv) := c in
  let: op := semop c in
  sem_cmd op m outv inv.

(* End high level language *)

(* -------------------------------------------------------------------- *)
(* ASM language                                                         *)

Variant register := R1 | R2 | R3.
Variant flag     : Set := CF.
Variant ireg     := IRReg of register | IRImm of int.

Axiom register_eqMixin : Equality.mixin_of register.
Canonical register_eqType := EqType _ register_eqMixin.

Axiom flag_eqMixin : Equality.mixin_of flag.
Canonical flag_eqType := EqType _ flag_eqMixin.

Axiom ireg_eqMixin : Equality.mixin_of ireg.
Canonical ireg_eqType := EqType _ ireg_eqMixin.

Variant low_instr :=
| ADDC_lo of register & ireg
| SUBC_lo of register & int
| MUL_lo
.

(* -------------------------------------------------------------------- *)
(* Low memory *)

Record lomem := {
  lm_reg : register -> int;
  lm_fgs : flag -> bool;
}.


Definition eval_reg (m: lomem) (r: register) : int := lm_reg m r.
Definition eval_flag (m: lomem) (f: flag) : bool := lm_fgs m f.
Definition write_flag (m: lomem) (f: flag) (b: bool) :=
  {| lm_reg := lm_reg m ; lm_fgs := λ f', if f' == f then b else lm_fgs m f' |}.
Definition write_reg  (m: lomem) (r: register) (v: int) : lomem :=
  {| lm_reg := λ r', if r' == r then v else lm_reg m r'; lm_fgs := lm_fgs m |}.

(* -------------------------------------------------------------------- *)
(* ASM Semantics                                                        *)

Definition eval_lit (m: lomem) (i: int) : int := i.
Definition eval_ireg  (m: lomem) (ir: ireg) : int := 
  match ir with
  | IRReg r => eval_reg m r
  | IRImm i => eval_lit m i
  end.

Definition sem_lo (m : lomem) (i : low_instr) : lomem :=
  match i with
  | ADDC_lo r x =>
      let v1 := eval_reg  m r in
      let v2 := eval_ireg m x in
      let c  := eval_flag m CF in

      let: (res, cf) := addc (v1, v2, c) in

      write_reg (write_flag m CF cf) r res

  | SUBC_lo r x =>
      let v1 := eval_reg  m r in
      let v2 := eval_lit m x in
      let c  := eval_flag m CF in

      let: (res, cf) := subc (v1, v2, c) in

      write_reg (write_flag m CF cf) r res

  | MUL_lo =>
    let x1 := eval_reg m R1 in
    let x2 := eval_reg m R2 in

    let: (y1, y2) := mul (x1, x2) in

    write_reg (write_reg m R1 y1) R2 y2
  end.

(* -------------------------------------------------------------------- *)
(* Compilation of variables                                             *) 
Variant destination :=
| DReg of register
| DFlag of flag.

Axiom destination_eqMixin : Equality.mixin_of destination.
Canonical destination_eqType := EqType _ destination_eqMixin.

Parameter var_of_register : register -> var.
Parameter var_of_flag : flag -> var.

Axiom var_of_uniq :
  uniq
    (map var_of_register [:: R1 ; R2 ; R3 ] ++ map var_of_flag [:: CF ]).

Axiom var_of_register_inj : ∀ x y,
  var_of_register x = var_of_register y →
  x = y.

Axiom var_of_flag_inj : ∀ x y,
  var_of_flag x = var_of_flag y →
  x = y.

Axiom var_of_register_var_of_flag : ∀ r f,
    ¬ var_of_register r = var_of_flag f.

Definition register_of_var (v: var) : option register :=
  if v == var_of_register R1 then Some R1 else
  if v == var_of_register R2 then Some R2 else
  if v == var_of_register R3 then Some R3 else
  None.

Lemma var_of_register_of_var v r :
  register_of_var v = Some r →
  var_of_register r = v.
Proof.
  rewrite /register_of_var.
  case: eqP; first by move => -> [] ->. move => _.
  case: eqP; first by move => -> [] ->. move => _.
  case: eqP; first by move => -> [] ->.
  done.
Qed.

Definition flag_of_var (v: var) : option flag :=
  if v == var_of_flag CF then Some CF else
  None.

Lemma var_of_flag_of_var v f :
  flag_of_var v = Some f →
  var_of_flag f = v.
Proof.
  by rewrite/flag_of_var; case: eqP => // -> [] <-.
Qed.

Definition compile_var (v: var) : option destination :=
  match register_of_var v with
  | Some r => Some (DReg r)
  | None =>
    match flag_of_var v with
    | Some f => Some (DFlag f)
    | None => None
    end
  end.

Definition vCF : var := var_of_flag CF.

Axiom compile_var_CF : compile_var vCF = Some (DFlag CF).
Axiom register_of_var_of_register :
  ∀ r, register_of_var (var_of_register r) = Some r.

(* -------------------------------------------------------------------- *)
Variant arg_ty := TYVar | TYLiteral | TYVL.

Definition interp_ty (ty : arg_ty) :=
  match ty with
  | TYVar     => register
  | TYLiteral => int
  | TYVL      => ireg
  end.

Fixpoint interp_tys (tys : seq arg_ty) :=
  if tys is ty :: tys then
    interp_ty ty -> interp_tys tys
  else low_instr.

Definition typed_apply_ireg {T} (ty: arg_ty) (arg: ireg) : 
  (interp_ty ty → T) → option T :=
  match ty, arg with
  | TYVar, IRReg r => λ op, Some (op r)
  | TYLiteral, IRImm i => λ op, Some (op i)
  | TYVL, _ => λ op, Some (op arg)
  | _, _ => λ _, None
  end.

Fixpoint typed_apply_iregs (tys: seq arg_ty) (iregs: seq ireg)
  : interp_tys tys -> option low_instr :=
  match tys, iregs with
  | [::], [::] => Some
  | ty :: tys', ir :: iregs' => λ op,
                          @typed_apply_ireg _ ty ir op >>=
                          @typed_apply_iregs tys' iregs'
  | _, _ => λ _, None
  end.


(* -------------------------------------------------------------------- *)
Variant arg_desc :=
| ADImplicit of var
| ADExplicit of nat.  (* FIXME: Add var option for instruction like SHL *)

Axiom arg_desc_eqMixin : Equality.mixin_of arg_desc.
Canonical arg_desc_eqType := EqType _ arg_desc_eqMixin.

Definition wf_implicit (ad: arg_desc) : bool :=
  if ad is ADImplicit x then
    compile_var x != None
  else true.

(* -------------------------------------------------------------------- *)
(* Generated ASM semantics                                              *)

Variant argument :=
| AReg of register
| AFlag of flag
| AInt of int.

Axiom argument_eqMixin : Equality.mixin_of argument.
Canonical argument_eqType := EqType argument argument_eqMixin.

Definition arg_of_dest (d: destination): argument :=
  match d with
  | DReg r => AReg r
  | DFlag f => AFlag f
  end.

Definition arg_of_ireg (i: ireg) : argument :=
  match i with
  | IRReg r => AReg r
  | IRImm i => AInt i
  end.

Definition sem_lo_ad_in (xs : seq ireg) (ad : arg_desc) : option argument :=
  match ad with
  | ADImplicit x => ssrfun.omap arg_of_dest (compile_var x)
  | ADExplicit n => ssrfun.omap arg_of_ireg (onth xs n)
  end.

Definition sem_lo_ad_out (xs : seq ireg) (ad : arg_desc) : option destination :=
  match ad with
  | ADImplicit x => compile_var x
  | ADExplicit n =>
      if onth xs n is Some (IRReg y) then Some (DReg y) else None
  end.

Definition eval_lo (m : lomem) (a : argument) : value :=
  match a with
  | AReg x => VInt (lm_reg m x)
  | AFlag f => VBool (lm_fgs m f)
  | AInt i => VInt i
  end.

Definition set_lo (d: destination) (v: value) (m: lomem) : option lomem :=
  match d, v with
  | DReg r, VInt i => Some (write_reg m r i)
  | DFlag f, VBool b => Some (write_flag m f b)
  | _, _ => None
  end.

Definition sets_lo (m : lomem) (x : seq destination) (v : seq value) :=
  if size x == size v then
    foldl (fun m xv => obind (set_lo xv.1 xv.2) m) (Some m) (zip x v)
  else None.

Definition sem_lo_cmd (op : seq value -> option (seq value)) m outv inv :=
  if op [seq eval_lo m x | x <- inv] is Some res then
    sets_lo m outv res
  else None.

Definition cmd_name_of_loid (loid: low_instr) : cmd_name :=
  match loid with
  | ADDC_lo _ _ => ADDC
  | SUBC_lo _ _ => SUBC
  | MUL_lo => MUL
  end.

Definition operands_of_loid (li: low_instr) : seq ireg :=
  match li with
  | ADDC_lo x y => [:: IRReg x ; y ]
  | SUBC_lo x y => [:: IRReg x ; IRImm y ]
  | MUL_lo => [::]
  end.

Definition sem_lo_gen_aux (m: lomem) 
     (c:cmd_name) (outx inx: seq arg_desc) (li: low_instr) : option lomem :=
  let xs := operands_of_loid li in
  let inx  := omap (sem_lo_ad_in xs) inx in
  let outx := omap (sem_lo_ad_out xs) outx in

  if (inx, outx) is (Some inx, Some outx) then
    sem_lo_cmd (semop c) m outx inx
  else None.

(* -------------------------------------------------------------------- *)

Definition wf_sem (c: cmd_name) (tys: seq arg_ty) (sem: interp_tys tys) : Prop :=
  ∀ irs loid,
    typed_apply_iregs irs sem = Some loid →
    cmd_name_of_loid loid = c ∧
    operands_of_loid loid = irs.

Definition gen_sem_correct (tys: seq arg_ty) id_name id_out id_in (sem:interp_tys tys) := 
  ∀ m irs loid,
    typed_apply_iregs irs sem = Some loid →
    sem_lo_gen_aux m id_name id_out id_in loid = Some (sem_lo m loid).     

Record instr_desc := {
  id_name : cmd_name;
  id_in   : seq arg_desc;
  id_out  : seq arg_desc;
  id_lo   : seq arg_ty;
  id_sem  : interp_tys id_lo;

  (* FIXME : Add the functionnal semantic of the operator in the record,
             this require to the have its syntatic type *)
  id_in_wf : all wf_implicit id_in;
  id_out_wf : all wf_implicit id_out;
  id_sem_wf: wf_sem id_name id_sem;
  id_gen_sem_wf : gen_sem_correct id_name id_out id_in id_sem;
}.

Definition sem_lo_gen (m: lomem) (id: instr_desc) (li: low_instr) : option lomem :=
  sem_lo_gen_aux m id.(id_name) id.(id_out) id.(id_in) li.

(* -------------------------------------------------------------------- *)
(* Generated mixed semantics                                            *)

Definition sem_ad_in (xs : seq expr) (ad : arg_desc) : option expr :=
  match ad with
  | ADImplicit x => Some (EVar x)
  | ADExplicit n => onth xs n
  end.

Definition sem_ad_out (xs : seq expr) (ad : arg_desc) : option var :=
  match ad with
  | ADImplicit x => Some x
  | ADExplicit n =>
      if onth xs n is Some (EVar y) then Some y else None
  end.

Definition sem_id
  (m : mem) (id : instr_desc) (xs : seq expr) : option mem :=
  let: inx  := omap (sem_ad_in xs) id.(id_in ) in
  let: outx := omap (sem_ad_out xs) id.(id_out) in

  if (inx, outx) is (Some inx, Some outx) then
    sem_cmd (semop id.(id_name)) m outx inx
  else None.

(* -------------------------------------------------------------------- *)
(* Definitions of descriptors                                           *)

Lemma eval_lo_arg_of_ireg m i :
  eval_lo m (arg_of_ireg i) = eval_ireg m i.
Proof. by case: i. Qed.

Definition evalrw := (compile_var_CF, eval_lo_arg_of_ireg).

Definition ADDC_desc : instr_desc. refine {|
  id_name := ADDC;
  id_in   := [:: ADExplicit 0; ADExplicit 1; ADImplicit vCF];
  id_out  := [:: ADExplicit 0; ADImplicit vCF];
  id_lo   := [:: TYVar; TYVL];
  id_sem  := ADDC_lo;
|}.
Proof.
  abstract by rewrite/= compile_var_CF.
  abstract by rewrite/= compile_var_CF.
  abstract by move => irs loid; case: irs => // [] // [] // x [] // y [] // [] <-.
  abstract 
    by move=> r [] // [] // x [] // y [] // loid [<-];
    rewrite /sem_lo_gen_aux /= ?evalrw /sem_lo_cmd /= ?evalrw;
    case: addc.
Defined.

Definition SUBC_desc : instr_desc. refine {|
  id_name := SUBC;
  id_in   := [:: ADExplicit 0; ADExplicit 1; ADImplicit vCF];
  id_out  := [:: ADExplicit 0; ADImplicit vCF];
  id_lo   := [:: TYVar; TYLiteral];
  id_sem  := SUBC_lo;
|}.
Proof.
  abstract by rewrite/= compile_var_CF.
  abstract by rewrite/= compile_var_CF.
  abstract by case => // [] // [] // x [] // [] // n [] // loid [] <-.
  abstract 
    by move=> r [] // [] // x [] // [] // n [] // loid [] <-;
    rewrite /sem_lo_gen_aux /= ?evalrw /sem_lo_cmd /= ?evalrw;
    case: subc.
Defined.

Definition MUL_desc : instr_desc. refine {|
  id_name := MUL;
  id_in   := [:: ADImplicit (var_of_register R1); ADImplicit (var_of_register R2)];
  id_out   := [:: ADImplicit (var_of_register R1); ADImplicit (var_of_register R2)];
  id_lo   := [::];
  id_sem  := MUL_lo;
|}.
Proof.
  abstract by rewrite/= /compile_var !register_of_var_of_register.
  abstract by rewrite/= /compile_var !register_of_var_of_register.
  abstract by move => [] // loid [] <-.
  abstract 
    by move => r [] // loid [] <-;
    rewrite /sem_lo_gen_aux /= /compile_var !register_of_var_of_register /=
    /sem_lo_cmd /=; case: mul.
Defined.

Definition get_id (c : cmd_name) :=
  match c with
  | ADDC => ADDC_desc
  | SUBC => SUBC_desc
  | MUL => MUL_desc
  end.

Lemma get_id_ok c : (get_id c).(id_name) = c.
Proof. by case: c. Qed.

(* -------------------------------------------------------------------- *)
(* High level to mixed semantics                                        *)

Definition check_cmd_arg (loargs : seq expr) (x : expr) (ad : arg_desc) :=
  match ad with
  | ADImplicit y => x == EVar y
  | ADExplicit n => (n < size loargs) && (x == nth x loargs n)
  end.

Definition check_cmd_res (loargs : seq expr) (x : var) (ad : arg_desc) :=
  match ad with
  | ADImplicit y => x == y
  | ADExplicit n => (n < size loargs) && (EVar x == nth (EVar x) loargs n)
  end.

Definition check_cmd_args
  (c : cmd_name) (outx : seq var) (inx : seq expr) (loargs : seq expr)
:=
  let: id := get_id c in

     all2 (check_cmd_res loargs) outx id.(id_out)
  && all2 (check_cmd_arg loargs) inx  id.(id_in ).

Lemma Pin (loargs hiargs : seq expr) (ads : seq arg_desc) :
     all2 (check_cmd_arg loargs) hiargs ads
  -> omap (sem_ad_in loargs) ads = Some hiargs.
Proof.
rewrite all2P => /andP [/eqP eqsz h];rewrite omap_map.
apply/eqP; rewrite oseqP.
apply/eqP/(eq_from_nth (x0 := None)); rewrite ?(size_map, eqsz) //.
move=> i lt_i_ads; have ad0 : arg_desc := (ADExplicit 0).
rewrite (nth_map ad0) // (nth_map (EVar vCF)) ?eqsz // /sem_ad_in.
set x1 := nth (EVar vCF) _ _; set x2 := nth ad0 _ _.
have -/(allP h) /=: (x1, x2) \in zip hiargs ads.
+ by rewrite -nth_zip // mem_nth // size_zip eqsz minnn.
rewrite /check_cmd_arg; case: x2 => [? /eqP->//|].
by move=> n /andP[len /eqP->];apply /eqP;rewrite (onth_sizeP x1).
Qed.

Lemma Pout (loargs : seq expr) (hiargs : seq var) (ads : seq arg_desc) :
     all2 (check_cmd_res loargs) hiargs ads
  -> omap (sem_ad_out loargs) ads = Some hiargs.
Proof.
rewrite all2P => /andP [/eqP eqsz h]; rewrite omap_map.
apply/eqP; rewrite oseqP.
apply/eqP/(eq_from_nth (x0 := None)); rewrite ?(size_map, eqsz) //.
move=> i lt_i_ads; have ad0 : arg_desc := (ADExplicit 0).
rewrite (nth_map ad0) // (nth_map vCF) ?eqsz // /sem_ad_out.
set x1 := nth vCF _ _; set x2 := nth ad0 _ _.
have -/(allP h) /=: (x1, x2) \in zip hiargs ads.
+ by rewrite -nth_zip // mem_nth // size_zip eqsz minnn.
rewrite /check_cmd_res; case: x2 => [? /eqP->//|].
by move=> n /andP[len /eqP];rewrite (onth_nth_size (EVar x1) len) => <-.
Qed.

Theorem L0 c outx inx loargs m1 m2 :
     check_cmd_args c outx inx loargs
  -> semc m1 (c, outx, inx) = Some m2
  -> sem_id m1 (get_id c) loargs = Some m2.
Proof.
by case/andP=> h1 h2; rewrite /sem_id /semc (Pin h2) (Pout h1) get_id_ok.
Qed.

Inductive source_position := 
  | InArgs of nat
  | InRes  of nat.

Definition get_loarg (outx: seq var) (inx:seq expr) (d:source_position) := 
  match d with
  | InArgs x => onth inx x
  | InRes  x => ssrfun.omap EVar (onth outx x)
  end.

(* FIXME: provide a more efficiant version of map on nat here *)
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
  | ADExplicit n => set_expr m n (p i)
  end.

Definition mk_loargs (c : cmd_name)  :=
  let: id := get_id c in
  let m := foldl (fun m p => compile_hi_arg InArgs p.1 p.2 m) (nempty _)
                 (zip id.(id_in) (iota 0 (size id.(id_in)))) in
  let m := foldl (fun m p => compile_hi_arg InRes p.1 p.2 m) m
                 (zip id.(id_out) (iota 0 (size id.(id_out)))) in 
  odflt [::] (omap (nget m) (iota 0 (size id.(id_lo)))).

Definition compile_hi_cmd (c : cmd_name) (outx : seq var) (inx : seq expr) := 
  let: id := get_id c in
  omap (get_loarg outx inx) (mk_loargs c) >>= fun loargs =>
    if check_cmd_args c outx inx loargs then Some loargs
    else None.

Lemma compile_hiP (c : cmd_name) (outx : seq var) (inx : seq expr) loargs :
  compile_hi_cmd c outx inx = Some loargs ->
  check_cmd_args c outx inx loargs.
Proof. by move=> /obindI [loargs'] [H1];case:ifP => // ? [<-]. Qed.

Theorem L1 c outx inx m1 m2 loargs :
     compile_hi_cmd c outx inx = Some loargs 
  -> semc m1 (c, outx, inx) = Some m2
  -> sem_id m1 (get_id c) loargs = Some m2.
Proof. by move=> /compile_hiP;apply L0. Qed.

(* -------------------------------------------------------------------- *)
(* Mixed semantics to generated ASM semantics                           *)

Variant lom_eqv (m : mem) (lom : lomem) :=
  | MEqv of
      (forall r, VInt  (lom.(lm_reg) r) = get m (var_of_register r))
    & (forall f, VBool (lom.(lm_fgs) f) = get m (var_of_flag f)).

Definition ireg_of_expr (arg: expr) : option ireg :=
  match arg with
  | EVar x => ssrfun.omap IRReg (register_of_var x)
  | EInt i => Some (IRImm i)
  end.

Lemma toto_in ads vs args irs m lom :
  lom_eqv m lom →
  all wf_implicit ads →
  omap ireg_of_expr vs = Some irs →
  omap (sem_ad_in vs) ads = Some args →
  ∃ loargs, omap (sem_lo_ad_in irs) ads = Some loargs ∧
  map (eval_lo lom) loargs = map (eval m) args.
Proof.
  move => eqm hwf hirs.
  elim: ads args hwf.
  - by move => args _ [] <-; exists [::].
  move => ad ads ih args' h; rewrite /= in h; case/andP: h => hwf hwf'.
  case/omap_consI => arg [] args [] -> ha has.
  case: (ih _ hwf' has) => {ih} loargs [hlo hlo'].
  case: ad ha hwf.
  + move => x /= [] ?; subst arg.
    case hd: compile_var => [ d | ] // _.
    exists (arg_of_dest d :: loargs); split; first by rewrite /= hlo.
    rewrite/=; f_equal => //.
    case: eqm => hr hf.
    move: hd; rewrite/compile_var.
    case eq1: register_of_var => [ r | ].
    * by case => <- /=; rewrite hr (var_of_register_of_var eq1).
    case eq2: flag_of_var => [ f | ] //.
    by case => <- /=; rewrite hf (var_of_flag_of_var eq2).
  move => /= x /onthP - /(_ (EInt 0)) /andP [] hx /eqP hx' _; subst arg.
  case: (onth_omap_size (EInt 0) hirs hx) => y [hy eqy].
  rewrite hy /= hlo /=.
  eexists; split; first by reflexivity.
  rewrite /=; f_equal => //.
  rewrite eval_lo_arg_of_ireg /=.
  case eqx: nth eqy => [ vx | i ]; last by case => <-.
  case: eqm => eqm _.
  by case eq1: register_of_var => [ z | ] // [] <-; rewrite eqm (var_of_register_of_var eq1).
Qed.

Lemma lom_eqv_set_register m lom x r i :
  lom_eqv m lom →
  register_of_var x = Some r →
  lom_eqv (set m x (VInt i)) (write_reg lom r i).
Proof.
  case => hr hf hx; rewrite -(var_of_register_of_var hx) => {x hx}.
  split => q; rewrite get_set /=.
  + case: eqP; first by move ->; rewrite eq_refl.
    move => ne; case: eqP => // /var_of_register_inj //.
  case: eqP => // h; elim: (var_of_register_var_of_flag (esym h)).
Qed.

Lemma lom_eqv_set_flag m lom x f b :
  lom_eqv m lom →
  flag_of_var x = Some f →
  lom_eqv (set m x (VBool b)) (write_flag lom f b).
Proof.
  case => hr hf hx; rewrite -(var_of_flag_of_var hx) => {x hx}.
  split => q; rewrite get_set /=.
  + case: eqP => // h; elim: (var_of_register_var_of_flag h).
  case: eqP; first by move ->; rewrite eq_refl.
  move => ne; case: eqP => // /var_of_flag_inj //.
Qed.

Lemma set_lom_eqv m lom x y v lom' :
  lom_eqv m lom →
  compile_var x = Some y →
  set_lo y v lom = Some lom' →
  lom_eqv (set m x v) lom'.
Proof.
  case => hr hf.
  rewrite /compile_var.
  case e1: register_of_var => [ r | ].
  + case => <-; case: v => // i [] <-.
    exact: lom_eqv_set_register.
  case e2: flag_of_var => // [ i ] [] <-; case: v => //= b [] <-.
  exact: lom_eqv_set_flag.
Qed.

Lemma sets_lo_cons m d ds v vs :
  sets_lo m (d :: ds) (v :: vs) = set_lo d v m >>= λ m', sets_lo m' ds vs.
Proof.
  rewrite {1} /sets_lo /=.
  case: set_lo; last by case: eqP => // _; exact: foldl_bind_None.
  case: eqP.
  + move/succn_inj => eq_sz /=.
     by move => m' /=; rewrite /sets_lo; case: eqP.
  move => ne_sz /= m'.
  by rewrite /sets_lo; case: eqP => // k; elim: ne_sz; rewrite k.
Qed.

Lemma toto_out ads vs out irs m1 lom1 outv m2 :
  lom_eqv m1 lom1 →
  all wf_implicit ads →
  omap ireg_of_expr vs = Some irs →
  omap (sem_ad_out vs) ads = Some out →
  sets m1 out outv = Some m2 →
  ∃ outx, omap (sem_lo_ad_out irs) ads = Some outx ∧
  ∃ lom2 : lomem, sets_lo lom1 outx outv = Some lom2 ∧ lom_eqv m2 lom2.
Proof.
  move => eqm hwf hirs.
  elim: ads out outv m1 lom1 eqm hwf.
  - move => out outv m1 lom1 eqm _ [] <- /setsI [hsz ->]; exists [::]; split => //.
    by case: outv hsz => // _; exists lom1.
  move => ad ads ih args' outv' m1 lom1 eqm h; rewrite /= in h; case/andP: h => hwf hwf'.
  case/omap_consI => arg [] args [] -> ha has /sets_consI [v] [outv] [? hm2]; subst outv'.
  case: ad ha hwf.
  + move => x /= [] ?; subst arg.
    case hd: compile_var => [ d | ] // _.
    have : ∃ lom', set_lo d v lom1 = Some lom'.
    admit.
    case => lom' hlom'.
    have eqm' := set_lom_eqv eqm hd hlom'.
    case: (ih args outv (set m1 x v) lom' eqm' hwf' has hm2)
      => dst [hdst] [lom2] [hlom2 eqm2].
    exists (d :: dst); split; first by rewrite hdst.
    exists lom2; split; first by rewrite sets_lo_cons hlom' /=. done.

  move => n /=.
  case eq1: onth => [ [] q | ] // [] ? _; subst q.
  move: eq1 => /onthP - /(_ (EInt 0)) /andP [] hsz /eqP harg.
  case: (onth_omap_size (EInt 0) hirs hsz) => y [hy]; rewrite harg.
  case eqy: register_of_var => [ y' | ] // - [] ?; subst y.
  have eqy' : compile_var arg = Some (DReg y') by rewrite /compile_var eqy.
  have : ∃ i, v = VInt i.
  admit.
  case => i ?; subst v.
  have : ∃ lom', set_lo (DReg y') i lom1 = Some lom' by eexists.
  case => lom' hlom'.
  have eqm' := set_lom_eqv eqm eqy' hlom'.
  have := ih _ _ _ _ eqm' hwf' has hm2.
  case => dst [hdst] [lom2] [hlom2 eqm2].
  rewrite hy hdst /=.
  eexists; split; first by reflexivity.
  case: hlom' => ?; subst lom'.
  by exists lom2.
Admitted.

(* -------------------------------------------------------------------- *)
Definition compile_lo (tys: seq arg_ty) (args: seq expr) (op: interp_tys tys) : option low_instr :=
  omap ireg_of_expr args >>= fun iregs =>
    @typed_apply_iregs tys iregs op.


Definition compile_gen (c : cmd_name) (args : seq expr) :=
  let id := get_id c in compile_lo args id.(id_sem).

Theorem L2 c vs m1 m2 loid lom1:
     compile_gen c vs = Some loid
  -> sem_id m1 (get_id c) vs = Some m2
  -> lom_eqv m1 lom1
  -> exists lom2, sem_lo_gen lom1 (get_id c) loid = Some lom2
  /\ lom_eqv m2 lom2.
Proof.
rewrite /compile_gen /sem_id => h.
case E1: (omap _) => [args|//].
case E2: (omap _) => [out|//].
rewrite get_id_ok; set op := (X in sem_cmd X).
rewrite /sem_cmd; case E3: (op _) => [outv|//].
rewrite /sem_lo_gen /sem_lo_gen_aux.
move: h. rewrite /compile_lo. case h: omap => // [irs] hirs.
rewrite (proj2 (id_sem_wf hirs)).
rewrite /sem_lo_cmd.
rewrite get_id_ok -/op.
move => hsets heqm.
have [ inx [ E4 E5 ] ] := toto_in heqm (id_in_wf _) h E1. rewrite E4.
have [ outx [ E6 [ lom2 [ E7 E8 ] ] ] ] := toto_out heqm (id_out_wf _) h E2 hsets.
rewrite E6 E5 E3. eauto.
Qed.

(* -------------------------------------------------------------------- *)
(* From generated ASM semantics to TCB ASM semantics                    *)

Lemma compile_cmd_name c vs loid :
  compile_gen c vs = Some loid →
  cmd_name_of_loid loid = c.
Proof.
  rewrite /compile_gen /compile_lo.
  case: omap => // irs h.
  have := @id_sem_wf (get_id c) irs loid h.
  rewrite get_id_ok.
  by case.
Qed.

Theorem L3 c vs m1 m2 loid lom :
     compile_gen c vs = Some loid
  -> sem_id m1 (get_id c) vs = Some m2
  -> lom_eqv m1 lom
  -> lom_eqv m2 (sem_lo lom loid).
Proof.
  move => hc.
  move/L2: (hc) => h/h{h} h/h{h} [lom'] [].
  rewrite -(compile_cmd_name hc).
  move /obindI : (hc) => [irs [? Hwt]].
  have := (id_gen_sem_wf lom Hwt).  
  by rewrite /sem_lo_gen (compile_cmd_name hc) => -> [<-].
Qed.

(* -------------------------------------------------------------------- *)
(* Putting all together                                                 *)

Definition compile (c : cmd_name) (outx : seq var) (inx:seq expr) := 
  compile_hi_cmd c outx inx >>= compile_gen c.

Theorem L (c : cmd_name) (outx : seq var) (inx : seq expr) loid (m1 m2 : mem) lom :
     compile c outx inx = Some loid 
  -> semc m1 (c, outx, inx) = Some m2
  -> lom_eqv m1 lom
  -> lom_eqv m2 (sem_lo lom loid).
Proof. 
  by move=> /obindI [lexprs []] /L1 H1 /L3 H3 /H1 /H3 H4 /H4.
Qed.
