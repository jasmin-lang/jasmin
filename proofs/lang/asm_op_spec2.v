(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import strings type var sem_type values sem_pexpr_params.
Require Import shift_kind sopn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

Section ASM_OP.

Context {pd: PointerData}.
Context `{asmop : asmOp}.

Variant asm_op_spec2 := 
| Oprotect of wsize
| Oset_msf 
| Oinit_msf 
| Omov_msf
| Oasm of asm_op_t.

Definition asm_op_spec2_beq (o1 o2:asm_op_spec2) :=
  match o1, o2 with
  | Oprotect ws1, Oprotect ws2 => ws1 == ws2 
  (*| Oprotect_ptr p1, Oprotect_ptr p2 => p1 == p2*)
  | Oset_msf, Oset_msf => true    
  | Oinit_msf, Oinit_msf => true
  | Omov_msf, Omov_msf => true 
  | Oasm o1, Oasm o2 => o1 == o2 ::>
  | _, _ => false
  end.

Lemma asm_op_spec2_eq_axiom : Equality.axiom asm_op_spec2_beq.
Proof.
Admitted.

Definition asm_op_spec2_eqMixin := Equality.Mixin asm_op_spec2_eq_axiom.
Canonical  asm_op_spec2_eqType  := EqType asm_op_spec2 asm_op_spec2_eqMixin.

(* The fields [i_in] and [i_out] are used in the regalloc pass only. The
   following instructions should be replaced before that pass (in lowering),
   thus we do not need to set those fields to true values. We respect the number
   of in- and out- arguments, but apart from that, we give some trivial values.
*)

Local Notation E n := (ADExplicit n None).

Definition init_msf : exec (pointer) := 
  ok (wrepr Uptr 0).

Definition Oinit_msf_instr := 
  mk_instr_desc (pp_s "init_msf")
                [:: ]
                [:: ]
                [:: sword Uptr]
                [:: E 0]
                init_msf
                [::].

Definition mov_msf (w:pointer) : exec (pointer) :=
  ok w.

Definition Omov_msf_instr := 
  mk_instr_desc (pp_s "mov_msf")
                [:: sword Uptr]
                [:: E 1]
                [:: sword Uptr]
                [:: E 0]
                mov_msf 
                [::].

Definition protect (ws:wsize) (w:word ws) (msf:pointer) : exec (word ws) := 
   if (msf == 0%R)%CMP then ok w 
       else if (msf == (-1)%R)%CMP 
            then let aux := (wrepr ws (-1)%Z) in ok aux
            else type_error.


Definition Oprotect_instr (ws:wsize) := 
  mk_instr_desc (pp_sz "protect" ws)
                [:: sword ws; sword Uptr]
                [:: E 1; E 2] (* irrelevant *)
                [:: sword ws]
                [:: E 0]      (* irrelevant *) 
                (@protect ws)
                [::].

Definition set_msf (b:bool) (w: pointer) : exec (pointer) := 
  let aux :=  wrepr Uptr (-1) in
  let w := if ~~b then aux else w in 
  ok (w).
 
Definition Oset_msf_instr := 
  mk_instr_desc (pp_s "set_msf")
                [:: sbool; sword Uptr]
                [:: E 0; E 1]
                [:: sword Uptr]
                [:: E 2]
                set_msf
                [::].


Definition get_instr_desc o :=
  match o with
  | Oprotect  sz   => Oprotect_instr sz
  (*| Oprotect_ptr p => Oprotect_ptr_instr p*)
  | Oset_msf       => Oset_msf_instr
  | Omov_msf       => Omov_msf_instr
  | Oinit_msf      => Oinit_msf_instr
  | Oasm o         => asm_op_instr o
  end.

Definition string_of_sopn o : string := str (get_instr_desc o) tt.

Definition sopn_tin o : list stype := tin (get_instr_desc o).
Definition sopn_tout o : list stype := tout (get_instr_desc o).
Definition sopn_sem  o := semi (get_instr_desc o).

Instance eqC_sopn : eqTypeC asm_op_spec2 :=
  { ceqP := asm_op_spec2_eq_axiom }.

Definition asm_op_spec1_prim_constructor (f:asm_op -> asm_op_spec2) (p : prim_constructor asm_op) : prim_constructor asm_op_spec2 :=
  match p with
  | PrimP x1 x2 => PrimP x1 (fun ws1 ws2 => f (x2 ws1 ws2))
  | PrimM x => PrimM (fun ws => f (x ws))
  | PrimV x => PrimV (fun ws1 s v ws2 => f (x ws1 s v ws2))
  | PrimX x => PrimX (fun ws1 ws2 ws3 => f (x ws1 ws2 ws3))
  | PrimVV x => PrimVV (fun ws1 v1 ws2 v2 ws3 => f (x ws1 v1 ws2 v2 ws3))
  | PrimARM x => PrimARM (fun sf ic hs => f (x sf ic hs))
  end.

Definition asm_op_spec1_prim_string : seq (string * prim_constructor asm_op_spec2) :=
  [::
    ("protect", PrimP Uptr (fun _ws sz => Oprotect sz));
    ("set_msf", PrimP Uptr (fun _ws sz => Oset_msf));
    ("init_msf", PrimP Uptr (fun _ws sz => Oinit_msf));
    ("mov_msf", PrimP Uptr (fun _ws sz => Omov_msf))
  ]%string
  ++ map (fun '(s, p) => (s, asm_op_spec1_prim_constructor Oasm p)) prim_string.

(* used in the OCaml world, it could be a definition it seems *)
Global Instance asmOp_spec2 : asmOp asm_op_spec2 :=
  { asm_op_instr := get_instr_desc;
    prim_string := asm_op_spec1_prim_string }.

End ASM_OP.

Section SEM_PEXPR_PARAMS.

  Context
    `{asmop : asmOp}
    {pd : PointerData}
    {syscall_state : Type}
    {fcp : flag_combination.FlagCombinationParams}
    {scs: syscall.syscall_sem syscall_state }.

#[export]
  Instance spp_of_asm_op_spec2 : SemPexprParams asm_op_spec2 syscall_state :=
    {
      _pd := pd;
      _asmop := asmOp_spec2;
      _fcp := fcp;
      _sc_sem := scs;
    }.

End SEM_PEXPR_PARAMS.

