From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require oseq.
Require Import ZArith
utils
strings wsize
memory_model
gen_map
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type
syscall
arch_decl
label
values.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* -------------------------------------------------------------------- *)
Variant sec_ty := 
  | Public
  | Transient 
  | Secret.

Definition vlvl := positive.

Variant sty := 
  | Sty  of sec_ty
  | Vlvl of vlvl.

Definition public := Sty Public.
Definition transient := Sty Transient.
Definition secret := Sty Secret.

Scheme Equality for sec_ty.

Lemma sec_ty_eq_axiom : Equality.axiom sec_ty_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_sec_ty_dec_bl.
  by apply: internal_sec_ty_dec_lb.
Qed.

Definition sec_ty_eqMixin     := Equality.Mixin sec_ty_eq_axiom.
Canonical  sec_ty_eqType      := Eval hnf in EqType sec_ty sec_ty_eqMixin.

Scheme Equality for sty.

Lemma sty_eq_axiom : Equality.axiom sty_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_sty_dec_bl.
  by apply: internal_sty_dec_lb.
Qed.

Definition sty_eqMixin     := Equality.Mixin sty_eq_axiom.
Canonical  sty_eqType      := Eval hnf in EqType sty sty_eqMixin.

Module CmpSecTy.

  Definition t : eqType := [eqType of sec_ty].

  Definition cmp (x y: t) : comparison := 
    match x, y with 
    | Public, Public => Eq 
    | Public, _      => Lt
    | Transient, Public => Gt
    | Transient, Transient => Eq 
    | Transient, Secret => Lt 
    | Secret, Secret => Eq 
    | Secret, _ => Gt
    end.

  Lemma cmpO : Cmp cmp.
  Proof.
    constructor.
    + by move=> [] [].
    + by move=> [] [] [] c //= [].
    by move=> [] [].
  Qed.

End CmpSecTy.

Module CmpSty.

  Definition t : eqType := [eqType of sty].

  Definition cmp (x y: t) : comparison := 
    match x, y with 
    | Sty sty1, Sty sty2 => CmpSecTy.cmp sty1 sty2
    | Sty _, Vlvl _ => Lt
    | Vlvl l1, Vlvl l2 => CmpPos.cmp l1 l2
    | Vlvl _, Sty _ => Gt
    end.

  Lemma cmpO : Cmp cmp.
  Proof.
  Admitted.

End CmpSty.

Module Msty := Mmake CmpSty.

Module Ssty := Smake CmpSty.

Definition pointsto := positive.




(* Set of constraints *)
Definition constraints := Msty.t Ssty.t.

Definition successors (c:constraints) (l:sty) := 
  odflt Ssty.empty (Msty.get c l).

Definition is_le (c:constraints) (l1 l2:sty) : bool := 
  Ssty.mem l2 (successors c l1).
  (* || l1 == public || l2 == secret *)

Definition is_clos_trans (c:constraints) := 
  forall x y z, 
    is_le c x y -> 
    is_le c y z -> 
    is_le c x z.

Definition check_clos_trans (c:constraints) := 
  Msty.all (fun l1 s => 
               Ssty.for_all (fun l2 => Ssty.subset (successors c l2) s) s) c.

(* TODO : forall c, check_clos_trans c -> is_clos_trans c *)

Record valid_c (c: constraints) := {
  vc_ct : is_clos_trans c;
  vc_bla (* FIXME *) : 
     ~(is_le c transient public) /\ ~(is_le c secret transient)
}.

Section TY_SYS.

Context {reg regx xreg rflag cond asm_op} {asm_d : asm reg regx xreg rflag cond asm_op}. 

Record env := 
  { e_reg  : FinMap.map (T:= reg_t)  (sty * wsize);
    e_regx : FinMap.map (T:= regx_t) (sty * wsize);
    e_xreg : FinMap.map (T:= xreg_t) (sty * wsize);
    e_flag : FinMap.map (T:= rflag_t) sty;
    e_pt   : Mp.t sty;
 }.

(* pt_size : size in bytes of a points-to *)
Definition pt_size := Mp.t positive.

(* Type system for arguments *)

(* Gamma |- e : ty, sty <= S *)

Section Expr.

Context (c:constraints) (env:env).

Definition wt_oreg (o:option reg_t) (S:Ssty.t) := 
  match 
Definition wt_addr (a:address) (S:Ssty.t) := 
  match a with
  | Areg ra =>
     
  | Arip _ => Ssty.for_all (fun l => is_le c public l) S
  Definition decode_reg_addr (s : asmmem) (a : reg_address) : pointer := nosimpl (
  let: disp   := a.(ad_disp) in
  let: base   := odflt 0%R (Option.map (s.(asm_reg)) a.(ad_base)) in
  let: scale  := word_of_scale a.(ad_scale) in
  let: offset := odflt 0%R (Option.map (s.(asm_reg)) a.(ad_offset)) in
  disp + base + scale * offset)%R.

Definition decode_addr (s:asmmem) (a:address) : pointer := 
  match a with
  | Areg ra => decode_reg_addr s ra
  | Arip ofs => (s.(asm_rip) + ofs)%R
  end.

Definition wt_asm_arg (k:addr_kind) (a:asm_arg) (ty:stype) (S:Ssty.t) := 
  match a, ty with
  | Condt cond, sbool => false (* FIXME *)
  | Imm _ _, sword _ => Ssty.for_all (fun l => is_le c public l) S

  | Reg r, sword ws  => 
      let (lr, ws') := env.(e_reg) r in
      Ssty.for_all (fun l => is_le c lr l) S && (ws <= ws')%CMP
  | Regx r, sword ws  => 
      let (lr, ws') := env.(e_regx) r in
      Ssty.for_all (fun l => is_le c lr l) S && (ws <= ws')%CMP

  | XReg r, sword ws  => 
      let (lr, ws') := env.(e_xreg) r in
      Ssty.for_all (fun l => is_le c lr l) S && (ws <= ws')%CMP

  | Addr a, sword ws =>
      
      if k is AK_compute then 
        wt_addr a S
      else 

  | _, _ => false
  end.


Variant asm_arg : Type :=
  | Condt  of cond_t
  | Imm ws of word ws
  | Reg    of reg_t
  | Regx   of regx_t
  | Addr   of address
  | XReg   of xreg_t.




 
