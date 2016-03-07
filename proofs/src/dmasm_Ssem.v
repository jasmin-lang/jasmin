(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import finmap strings dmasm_utils dmasm_type dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.

(* ** Type interpretation
 * -------------------------------------------------------------------- *)

Definition array (T:Type) := nat -> T.
Definition acnst {T} (t:T) : array T := fun i => t.
Definition aget {T} (a:array T) (i:nat) := a i.
Definition aset {T} (a:array T) (i:nat) (v:T) :=
  fun j => if i == j  then v else a i.

Fixpoint sst2ty (t : stype) : Type :=
  match t with
  | sword         => word
  | sbool         => bool
  | sprod st1 st2 => ((sst2ty st1) * (sst2ty st2))%type
  | sarr n st     => array (sst2ty st)
  end.

Fixpoint sdflt_val st :  sst2ty st :=
  match st with
  | sword         => n2w 0
  | sbool         => true
  | sprod st1 st2 => (sdflt_val st1, sdflt_val st2)
  | sarr n st     => acnst (sdflt_val st)
  end.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation svmap     := (g_vmap sst2ty).
Definition svmap_set {st} vm id v := nosimpl (@g_vmap_set sst2ty st vm id v).
Definition svmap_get vm st id := nosimpl (@g_vmap_get sst2ty vm st id).
Notation svmap0    := (@g_vmap0 sst2ty sdflt_val).

Delimit Scope svmap_scope with svmap.
Local Open Scope svmap_scope.
Notation "vm .[ st , id ]" := (svmap_get vm st id) : svmap_scope.
Notation "vm .[ k  <- v ]" := (svmap_set vm k v) : svmap_scope.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition ssem_sop st1 st2 (sop : sop st1 st2) : sst2ty st1 -> sst2ty st2 :=
  match sop in sop st1_ st2_ return sst2ty st1_ -> sst2ty st2_ with
  | Oand       => fun x => x.1 && x.2
  | Onot       => negb
  | Ofst t1 t2 => fst
  | Osnd t1 t2 => snd
  | Oadd       =>
    fun x => let n := (x.1 + x.2)%nat in (n >= 2^wsize,n%:R)
  | Oaddc      =>
    fun x => 
             let n := (x.1.1 + x.1.2 + x.2)%nat in 
             (n >= 2^wsize,n%:R)
  | Oeq        => fun x => x.1 == x.2
  | Olt        => fun x => x.1 < x.2
  | Oget n     => fun x =>  let a := x.1 in let i := w2n x.2 in aget a i
  | Oset n     =>
    fun x => let: (a,wi,v) := x in
             let i := w2n wi in
             aset a i v
  end.

Fixpoint ssem_pexpr {st} (vm : svmap) (pe : pexpr st) : sst2ty st :=
  match pe with
  | Pvar st v => vm.[st,vname v]
  | Pconst c  => c
  | Papp sta str so pe =>
      ssem_sop so (ssem_pexpr vm pe)
  | Ppair st1 st2 pe1 pe2 =>
      (ssem_pexpr vm pe1, ssem_pexpr vm pe2)
  end.

(* ** Writing local variables
 * -------------------------------------------------------------------- *)

Definition swrite_subst := @g_write_subst sst2ty (fun t1 t2 =>  fst) (fun t1 t2 => snd).

Definition swrite_vmap :=
  foldr (fun (ts:g_tosubst sst2ty) vm =>
          let (t,id,v) := ts in
          vm.[id <- v]).

Definition swrite_rval {st} (vm:svmap) (l:rval st) (v:sst2ty st) :=
   swrite_vmap vm (swrite_subst l v [::]).

(* ** Instructions
 * -------------------------------------------------------------------- *)

Record sestate := SEstate {
  semem : mem;
  sevm  : svmap
}.

Definition ssem_bcmd (es : sestate) (bc : bcmd) : exec sestate :=
  match bc with
  | Assgn st rv pe =>
      let v := ssem_pexpr es.(sevm) pe in
      let vm := swrite_rval es.(sevm) rv v in
      ok (SEstate es.(semem) vm)
  | Load rv pe_addr =>
      let p := ssem_pexpr es.(sevm) pe_addr in
      read_mem es.(semem) p >>= fun w =>
      let vm := swrite_rval es.(sevm) rv w in
      ok (SEstate es.(semem) vm)

  | Store pe_addr pe_val =>
      let p := ssem_pexpr es.(sevm) pe_addr in
      let w := ssem_pexpr es.(sevm) pe_val in
      write_mem es.(semem) p w >>= fun m =>
      ok (SEstate m es.(sevm))
  end.

Definition ssem_range (vm : svmap) (r : range) :=
  let: (d,pe1,pe2) := r in
  let w1 := ssem_pexpr vm pe1 in
  let w2 := ssem_pexpr vm pe2 in
  let n1 := w2n w1 in
  let n2 := w2n w2 in
  ok [seq n2w n | n <- wrange d n1 n2].

Inductive ssem : sestate -> cmd -> sestate -> Prop :=
| SEskip s :
    ssem s [::] s

| SEseq s1 s2 s3 i c :
    ssem_i s1 i s2 -> ssem s2 c s3 -> ssem s1 (i::c) s3

with ssem_i : sestate -> instr -> sestate -> Prop :=
| SEbcmd s1 s2 c:
    ssem_bcmd s1 c = ok s2 -> ssem_i s1 (Cbcmd c) s2

| SEifTrue s1 s2 (pe : pexpr sbool) c1 c2 :
    ssem_pexpr s1.(sevm) pe ->
    ssem s1 c1 s2 ->
    ssem_i s1 (Cif pe c1 c2) s2

| SEifFalse s1 s2 (pe : pexpr sbool) c1 c2 :
    ~~ssem_pexpr s1.(sevm) pe ->
    ssem s1 c2 s2 ->
    ssem_i s1 (Cif pe c1 c2) s2

| SEcall m1 m2 vm1 vmc1 vmc2 starg stres farg fres fbody rv_res pe_arg :
    let arg := ssem_pexpr vm1 pe_arg in
    let vmc1 := swrite_rval vmc1 farg arg in
    ssem (SEstate m1 vmc1) fbody (SEstate m2 vmc2) ->
    let res := ssem_pexpr vmc2 fres in
    let vm2 := swrite_rval vm1 rv_res res in
    ssem_i (SEstate m1 vm1)
        (@Ccall starg stres rv_res (FunDef farg fbody fres) pe_arg)
        (SEstate m2 vm2)

| SEforDone s1 s2 iv rng c ws :
    ssem_range s1.(sevm) rng = ok ws ->
    ssem_for iv ws s1 c s2 ->
    ssem_i s1 (Cfor iv rng c) s2

with ssem_for : var sword -> seq word -> sestate -> cmd -> sestate -> Prop :=

| SEForDone s c iv :
    ssem_for iv [::] s c s

| SEForOne s1 s2 s3 c w ws iv :
    let ac := Cbcmd (Assgn (Rvar iv) (Pconst w)) :: c in
    ssem                s1 ac s2 ->
    ssem_for iv (ws)    s2 c  s3 ->
    ssem_for iv (w::ws) s1 c  s3.
