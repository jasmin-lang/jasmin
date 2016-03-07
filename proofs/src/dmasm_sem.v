(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import finmap strings dmasm_utils dmasm_type dmasm_var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope fset.
Local Open Scope fmap.

(* ** Types for values
 * -------------------------------------------------------------------- *)

Definition wsize : nat := nosimpl 64.

Definition word := 'Z_(2^wsize).
Definition w2n (w : word) : nat := w.
Definition n2w (n : nat) : word :=  n%:R.

Lemma codeK_word : cancel w2n n2w.
Proof. rewrite /cancel /w2n /n2w => x. by rewrite natr_Zp. Qed.
Definition word_eqMixin     := comparableClass (@LEM word).
Canonical  word_eqType      := Eval hnf in EqType word word_eqMixin.
Definition word_choiceMixin := CanChoiceMixin codeK_word.
Canonical  word_choiceType  := ChoiceType word word_choiceMixin.

(* ** Syntax
 * -------------------------------------------------------------------- *)

Inductive sop : stype -> stype -> Set :=
(* bools *)
| Oand  : sop (sbool ** sbool) sbool
| Onot  : sop sbool sbool
(* pairs *)
| Ofst  : forall st1 st2, sop (st1 ** st2) st1
| Osnd  : forall st1 st2, sop (st1 ** st2) st2
(* words *)
| Oadd  : sop (sword ** sword)          (sbool ** sword)
| Oaddc : sop (sword ** sword ** sbool) (sbool ** sword)
| Oeq   : sop (sword ** sword) sbool
| Olt   : sop (sword ** sword) sbool
(* arrays *)
| Oset  : forall n, sop (sarr n sword ** sword ** sword) (sarr n sword)
| Oget  : forall n, sop (sarr n sword ** sword)          sword.

Inductive pexpr : stype -> Type :=
| Pvar   : forall x:var, pexpr x.(vtype)
| Pconst : word -> pexpr sword
| Ppair  : forall st1 st2, pexpr st1 -> pexpr st2 -> pexpr (st1 ** st2)
| Papp   : forall starg stres: stype, sop starg stres -> pexpr starg -> pexpr stres.

Inductive rval : stype -> Set :=
| Rvar  : forall (x:var), rval x.(vtype)
| Rpair : forall st1 st2, rval st1 -> rval st2 -> rval (st1 ** st2).

Inductive bcmd :=
| Assgn : forall st, rval st -> pexpr st -> bcmd
| Load  : rval sword -> pexpr sword -> bcmd
| Store : pexpr sword -> pexpr sword -> bcmd.

Inductive dir := UpTo | DownTo.

Definition range := (dir * pexpr sword * pexpr sword)%type.

Inductive instr := 
| Cbcmd  : bcmd -> instr
| Cif    : pexpr sbool -> seq instr -> seq instr -> instr
| Cfor   : rval sword -> range -> seq instr -> instr
| Ccall  : forall starg stres, 
             rval  stres ->
             fundef starg stres ->
             pexpr starg ->
             instr

with fundef : stype -> stype -> Type := 
| FunDef : forall starg stres, rval starg -> seq instr -> pexpr stres -> fundef starg stres.

Notation cmd := (seq instr).

Definition fd_arg sta str (fd : fundef sta str) : rval sta :=
  match fd with FunDef _ _ fa _ _ => fa end.

Definition fd_body sta str (fd : fundef sta str) : cmd :=
  match fd with FunDef _ _ _ fb _ => fb end.

Definition fd_res sta str (fd : fundef sta str) : pexpr str :=
  match fd with FunDef _ _ _ _ fr => fr end.

Section IND.
  Variable Pi : instr -> Type.
  Variable Pc : cmd -> Type.
  Variable Pf : forall ta tr, fundef ta tr -> Type.

  Hypothesis Hskip : Pc [::].
  Hypothesis Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Hypothesis Hbcmd : forall bc,  Pi (Cbcmd bc).
  Hypothesis Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Hypothesis Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Hypothesis Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Hypothesis Hfunc : forall ta tr (x:rval ta) c (re:pexpr tr), Pc c -> Pf (FunDef x c re).

  Fixpoint instr_rect' (i:instr) : Pi i := 
    match i return Pi i with
    | Cbcmd bc => Hbcmd bc
    | Cif b c1 c2 =>
      Hif b
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c1)
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c2)
    | Cfor i rn c =>
      Hfor i rn 
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c)
    | Ccall ta tr x f a =>
      Hcall x a (func_rect f)
    end
  with func_rect {ta tr} (f:fundef ta tr) : Pf f := 
    match f with
    | FunDef ta tr x c re => 
      Hfunc x re
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c)
    end.

  Definition cmd_rect c := 
    list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c.

End IND.

Definition cmd_ind (P:cmd -> Prop) (Pf:forall ta tr, fundef ta tr -> Prop) := 
  @cmd_rect (fun i => P [::i]) P Pf.

Definition func_ind (P:cmd -> Prop) (Pf:forall ta tr, fundef ta tr -> Prop) := 
  @func_rect (fun i => P [::i]) P Pf.

Definition assgn st (rv : rval st) pe := Cbcmd (Assgn rv pe).
Definition load rv pe := Cbcmd (Load rv pe).
Definition store pe1 pe2 := Cbcmd (Store pe1 pe2).


(* ** Interpretation of types
 * -------------------------------------------------------------------- *)

Fixpoint st2ty (t : stype) : Type :=
  match t with
  | sword         => word
  | sbool         => bool
  | sprod st1 st2 => ((st2ty st1) * (st2ty st2))%type
  | sarr n st     => (n.+1).-tuple (st2ty st) (* do not allow zero-dim arrays *)
  end.

(* ** Default values
 * -------------------------------------------------------------------- *)

Fixpoint dflt_val (st : stype) : st2ty st :=
  match st with
  | sword         => n2w 0
  | sbool         => false
  | sprod st1 st2 => (dflt_val st1, dflt_val st2)
  | sarr n    st  => [tuple (dflt_val st) | i < n.+1]
  end.

Definition rdflt_ (st : stype) e (r : result e (st2ty st)) : st2ty st :=
  rdflt (dflt_val st) r.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Record g_vmap (to : stype -> Type) := Vmap {
  vm_map : forall x, to x.(vtype)
}.

Definition g_vmap_set (to:stype -> Type) (vm : g_vmap to) x (v : to x.(vtype)) : g_vmap to :=
  Vmap
    (fun y =>
       match (x =P y) with
       | ReflectT eq => 
         eq_rect x (fun x => to x.(vtype)) v y eq
       | _           => vm.(vm_map) y
       end).

Definition g_vmap0 to (dval : forall x, to x.(vtype)) : g_vmap to := 
  Vmap (fun x => dval x).

Definition g_vmap_get to (vm : g_vmap to) x :=
  vm.(vm_map) x.

Notation vmap     := (g_vmap st2ty).
Notation vmap0    := (@g_vmap0 st2ty dflt_val).
Definition vmap_set  vm x v := nosimpl (@g_vmap_set st2ty vm x v).
Definition vmap_get vm x := nosimpl (@g_vmap_get st2ty vm x).

Definition vmap_ext_eq (vm1 vm2 : vmap) :=
  forall x, vmap_get vm1 x = vmap_get vm2 x.

Delimit Scope vmap_scope with vmap.
Local Open Scope vmap_scope.
Notation "vm .[ id ]" := (vmap_get vm id) : vmap_scope.
Notation "vm .[ k  <- v ]" := (@vmap_set vm k v) : vmap_scope.
Notation "vm1 =v vm2" := (vmap_ext_eq vm1 vm2) (at level 70, no associativity) : vmap_scope.

(* There are probably many better ways to do this ... *)
Axiom vmap_ext: forall (vm1 vm2 : vmap), vm1 =v vm2 -> vm1 = vm2.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Inductive error := ErrOob | ErrAddrUndef | ErrAddrInvalid.

Definition exec t := result error t.
Definition ok := Ok error. 

Definition sem_sop st1 st2 (sop : sop st1 st2) : st2ty st1 -> exec (st2ty st2) :=
  match sop in sop st1 st2 return st2ty st1 -> exec (st2ty st2) with
  | Oand       => fun xy => ok (xy.1 && xy.2)
  | Onot       => fun b => ok (~~ b)
  | Ofst t1 t2 => fun xy => ok xy.1
  | Osnd t1 t2 => fun xy => ok xy.2
  | Oadd       => fun xy =>
                    let n := (xy.1 + xy.2)%nat in
                    ok (n >= 2^wsize,n%:R)
  | Oaddc      => fun xy_b =>
                    let n := (xy_b.1.1 + xy_b.1.2 + xy_b.2)%nat in
                    ok (n >= 2^wsize,n%:R)
  | Oeq        => fun xy => ok (xy.1 == xy.2)
  | Olt        => fun xy => ok (xy.1 < xy.2)
  | Oget n     => fun ai =>
                    let i := w2n ai.2 in
                    if i > n
                    then Error ErrOob
                    else ok (tnth ai.1 (@inZp n i))
  | Oset n     => fun a_i_v =>
                    let i := w2n a_i_v.1.2 in
                    if i > n
                    then Error ErrOob
                    else
                      ok [tuple (if j == inZp i then a_i_v.2 else tnth a_i_v.1.1 j) | j < n.+1]
  end.

Fixpoint sem_pexpr st (vm : vmap) (pe : pexpr st) : exec (st2ty st) :=
  match pe with
  | Pvar v => ok (vm.[ v ])
  | Pconst c => ok c
  | Papp sta str so pe =>
      sem_pexpr vm pe >>= fun v =>
      (sem_sop so) v
  | Ppair st1 st2 pe1 pe2 =>
      sem_pexpr vm pe1 >>= fun v1 =>
      sem_pexpr vm pe2 >>= fun v2 =>
      ok (v1,v2)
  end.

(* ** Writing local variables
 * -------------------------------------------------------------------- *)

Section WRITE.

  Variable to : stype -> Type.
 
  Record g_tosubst  := ToSubst {
    ts_v  : var;
    ts_to : to ts_v.(vtype);
  }.

  Variable fst : forall {t1 t2:stype}, to (t1 ** t2) -> to t1.
  Variable snd : forall {t1 t2:stype}, to (t1 ** t2) -> to t2.

  Fixpoint g_write_subst {st} (l:rval st) : to st -> list g_tosubst -> list g_tosubst := 
    match l in rval st_ return to st_ -> list g_tosubst -> list g_tosubst with
    | Rvar x => fun v s =>  (@ToSubst x v) :: s
    | Rpair t1 t2 rv1 rv2 => fun v s => 
      g_write_subst rv2 (snd v) (g_write_subst rv1 (fst v) s)
    end.

End WRITE.

Definition write_subst := @g_write_subst st2ty (fun t1 t2 => fst) (fun t1 t2 => snd).

Definition write_vmap := 
  foldr (fun (ts:g_tosubst st2ty) vm => vm.[ts.(ts_v) <- ts.(ts_to)]).

Definition write_rval {st} (vm:vmap) (l:rval st) (v:st2ty st) :=
  write_vmap vm (write_subst l v [::]).
  
(* ** Memory
 * -------------------------------------------------------------------- *)

Definition mem := {fmap word -> word}.

Variable valid_addr : word -> bool.

Definition read_mem (m : mem) (p : word) : exec word :=
  if valid_addr p
  then o2r ErrAddrUndef (m.[? p])
  else Error ErrAddrInvalid.

Definition write_mem (m : mem) (p w : word) : exec mem :=
  if valid_addr p
  then ok (m.[p <- w]%fmap)
  else Error ErrAddrInvalid.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition sem_bcmd (es : estate) (bc : bcmd) : exec estate :=
  match bc with
  | Assgn st rv pe =>
      sem_pexpr es.(evm) pe >>= fun v =>
      let vm := write_rval es.(evm) rv v in
      ok (Estate es.(emem) vm)
  | Load rv pe_addr =>
      sem_pexpr es.(evm) pe_addr >>= fun p =>
      read_mem es.(emem) p >>= fun w =>
      let vm := write_rval es.(evm) rv w in
      ok (Estate es.(emem) vm)

  | Store pe_addr pe_val =>
      sem_pexpr es.(evm) pe_addr >>= fun p =>
      sem_pexpr es.(evm) pe_val  >>= fun w =>
      write_mem es.(emem) p w >>= fun m =>
      ok (Estate m es.(evm))
  end.

Definition wrange d n1 n2 :=
  let idxs := iota n1 (n2 - n1) in
  match d with
  | UpTo   => idxs
  | DownTo => rev idxs (* [seq (n1 + (n2 - n - 1))%nat | n <- idxs ] *)
  end.

Definition sem_range (vm : vmap) (r : range) :=
  let: (d,pe1,pe2) := r in
  sem_pexpr vm pe1 >>= fun w1 =>
  sem_pexpr vm pe2 >>= fun w2 =>
  let n1 := w2n w1 in
  let n2 := w2n w2 in
  ok [seq n2w n | n <- wrange d n1 n2].

Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
    sem s [::] s

| Eseq s1 s2 s3 i c :
    sem_i s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

with sem_i : estate -> instr -> estate -> Prop :=

| Ebcmd s1 s2 c:
    sem_bcmd s1 c = ok s2 -> sem_i s1 (Cbcmd c) s2

| Eif s1 s2 (pe : pexpr sbool) cond c1 c2 :
    sem_pexpr s1.(evm) pe = ok cond ->
    sem s1 (if cond then c1 else c2) s2 ->
    sem_i s1 (Cif pe c1 c2) s2

| Ecall m1 m2 vm1 vmc0 vmc2 starg stres farg fres fbody rv_res pe_arg :
    isOk (@sem_pexpr starg vm1 pe_arg) ->
    let arg := rdflt_ (@sem_pexpr starg vm1 pe_arg) in
    let vmc1 := @write_rval starg vmc0 farg arg in
    sem (Estate m1 vmc1) fbody (Estate m2 vmc2)->
    isOk (@sem_pexpr stres vmc2 fres) ->
    sem_i (Estate m1 vm1)
          (@Ccall starg stres rv_res (FunDef farg fbody fres) pe_arg)
          (Estate m2
             (@write_rval stres vm1 rv_res (rdflt_ (@sem_pexpr stres vmc2 fres))))

| EFor s1 s2 iv rng c ws :
    sem_range s1.(evm) rng = ok ws ->
    sem_for iv ws s1 c s2 ->
    sem_i s1 (Cfor iv rng c) s2

with sem_for : rval sword -> seq word -> estate -> cmd -> estate -> Prop :=

| EForDone s c iv :
    sem_for iv [::] s c s

| EForOne s1 s2 s3 c w ws iv :
    let ac := Cbcmd (Assgn iv (Pconst w)) :: c in
    sem                s1 ac s2 ->
    sem_for iv (ws)    s2 c  s3 ->
    sem_for iv (w::ws) s1 c  s3.

Scheme sem_Ind := Minimality for sem Sort Prop
with sem_i_Ind := Minimality for sem_i Sort Prop
with sem_for_Ind := Minimality for sem_for Sort Prop.

Lemma sem_inv_app l1 l2 s1 s2:
  sem s1 (l1 ++ l2) s2 ->
  exists s3,
    sem s1 l1 s3 /\ sem s3 l2 s2.
Proof.
  generalize s1.
  elim l1.
  + move=> s1_. rewrite /= => H.
    by exists s1_; split; first by constructor.
  + move=> inst c Hi s1_ Hs.
    rewrite cat_cons in Hs.
    inversion Hs => {Hs}.
    move: (Hi _ H4). elim => s5. case => Hs1 Hs2.
    exists s5. split => //.
    by apply (Eseq (s2:=s3)).
Qed.
