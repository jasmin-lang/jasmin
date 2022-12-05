(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import strings type var sem_type values.
Require Import shift_kind.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

(* ----------------------------------------------------------------------------- *)

Variant implicit_arg : Type :=
  | IArflag of var
  | IAreg   of var
  .

Variant arg_desc :=
| ADImplicit  of implicit_arg
| ADExplicit  of nat & option var.

Record instruction_desc := mkInstruction {
  str      : unit -> string;
  tin      : list stype;
  i_in     : seq arg_desc;
  tout     : list stype;
  i_out    : seq arg_desc;
  semi     : sem_prod tin (exec (sem_tuple tout));
  semu     : forall vs vs' v,
                List.Forall2 value_uincl vs vs' ->
                app_sopn_v semi vs = ok v ->
                exists2 v', app_sopn_v semi vs' = ok v' & List.Forall2 value_uincl v v';
  i_safe   : seq safe_cond;
}.

Arguments semu _ [vs vs' v] _ _.

Notation mk_instr_desc str tin i_in tout i_out semi safe :=
  {| str      := str;
     tin      := tin;
     i_in     := i_in;
     tout     := tout;
     i_out    := i_out;
     semi     := semi;
     semu     := @vuincl_app_sopn_v tin tout semi refl_equal;
     i_safe   := safe;
  |}.

Variant prim_constructor (asm_op:Type) :=
  | PrimP of wsize & (option wsize -> wsize -> asm_op)
  | PrimM of (option wsize -> asm_op)
  | PrimV of (option wsize -> signedness -> velem -> wsize -> asm_op)
  | PrimX of (option wsize -> wsize -> wsize -> asm_op)
  | PrimVV of (option wsize -> velem -> wsize -> velem -> wsize -> asm_op)
  | PrimARM of (bool -> bool -> option shift_kind -> asm_op)
  .

Class asmOp (asm_op : Type) := {
  _eqT           :> eqTypeC asm_op
  ; asm_op_instr : asm_op -> instruction_desc
  ; prim_string   : list (string * prim_constructor asm_op)
}.

Definition asm_op_t {asm_op} {asmop : asmOp asm_op} := asm_op.

Section ASM_OP.

Context {pd: PointerData}.
Context `{asmop : asmOp}.

(* Instructions that must be present in all the architectures. *)
Variant sopn :=
| Ocopy     of wsize & positive
| Onop
| Omulu     of wsize   (* cpu   : [sword; sword]        -> [sword;sword] *)
| Oaddcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Osubcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Oasm      of asm_op_t.

Definition sopn_beq (o1 o2:sopn) :=
  match o1, o2 with
  | Ocopy ws1 p1, Ocopy ws2 p2 => (ws1 == ws2) && (p1 == p2)
  | Onop, Onop => true
  | Omulu ws1, Omulu ws2 => ws1 == ws2
  | Oaddcarry ws1, Oaddcarry ws2 => ws1 == ws2
  | Osubcarry ws1, Osubcarry ws2 => ws1 == ws2
  | Oasm o1, Oasm o2 => o1 == o2 ::>
  | _, _ => false
  end.

Lemma sopn_eq_axiom : Equality.axiom sopn_beq.
Proof.
  move=> [ws1 p1||ws1|ws1|ws1|o1] [ws2 p2||ws2|ws2|ws2|o2] /=;
   first (by apply (iffP andP) => [[/eqP -> /eqP ->] | [-> ->]]);
   try by (constructor || apply: reflect_inj eqP => ?? []).
Qed.

Definition sopn_eqMixin := Equality.Mixin sopn_eq_axiom.
Canonical  sopn_eqType  := EqType sopn sopn_eqMixin.

(* The fields [i_in] and [i_out] are used in the regalloc pass only. The
   following instructions should be replaced before that pass (in lowering),
   thus we do not need to set those fields to true values. We respect the number
   of in- and out- arguments, but apart from that, we give some trivial values.
*)

Local Notation E n := (ADExplicit n None).

Definition Ocopy_instr ws p := 
  let sz := Z.to_pos (arr_size ws p) in
  {| str      := pp_sz "copy" ws;
     tin      := [:: sarr sz];
     i_in     := [:: E 1];
     tout     := [:: sarr sz];
     i_out    := [:: E 0];
     semi     := @WArray.copy ws p;
     semu     := @vuincl_copy ws p;
     i_safe   := [:: AllInit ws p 0];
  |}.

Definition Onop_instr := 
  mk_instr_desc (pp_s "NOP")
           [::] [::]
           [::] [::]
           (ok tt)
           [::].

Definition Omulu_instr sz :=
  mk_instr_desc (pp_sz "mulu" sz)
           [:: sword sz; sword sz]
           [:: E 0; E 1] (* this info is irrelevant *)
           [:: sword sz; sword sz]
           [:: E 2; E 3] (* this info is irrelevant *)
           (fun x y => ok (@wumul sz x y)) [::].
 
Definition Oaddcarry_instr sz :=
  mk_instr_desc (pp_sz "adc" sz)
           [:: sword sz; sword sz; sbool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: sbool; sword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (fun x y c => let p := @waddcarry sz x y c in ok (Some p.1, p.2))
           [::].

Definition Osubcarry_instr sz:= 
  mk_instr_desc (pp_sz "sbb" sz)
           [:: sword sz; sword sz; sbool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: sbool; sword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (fun x y c => let p := @wsubcarry sz x y c in ok (Some p.1, p.2))
           [::].

Definition get_instr_desc o :=
  match o with
  | Ocopy ws p   => Ocopy_instr ws p
  | Onop         => Onop_instr
  | Omulu     sz => Omulu_instr sz
  | Oaddcarry sz => Oaddcarry_instr sz
  | Osubcarry sz => Osubcarry_instr sz
  | Oasm o       => asm_op_instr o
  end.

Definition string_of_sopn o : string := str (get_instr_desc o) tt.

Definition sopn_tin o : list stype := tin (get_instr_desc o).
Definition sopn_tout o : list stype := tout (get_instr_desc o).
Definition sopn_sem  o := semi (get_instr_desc o).

Instance eqC_sopn : eqTypeC sopn :=
  { ceqP := sopn_eq_axiom }.

Definition map_prim_constructor {A B} (f: A -> B) (p : prim_constructor A) : prim_constructor B :=
  match p with
  | PrimP x1 x2 => PrimP x1 (fun ws1 ws2 => f (x2 ws1 ws2))
  | PrimM x => PrimM (fun ws => f (x ws))
  | PrimV x => PrimV (fun ws1 s v ws2 => f (x ws1 s v ws2))
  | PrimX x => PrimX (fun ws1 ws2 ws3 => f (x ws1 ws2 ws3))
  | PrimVV x => PrimVV (fun ws1 v1 ws2 v2 ws3 => f (x ws1 v1 ws2 v2 ws3))
  | PrimARM x => PrimARM (fun sf ic hs => f (x sf ic hs))
  end.

Definition sopn_prim_string : seq (string * prim_constructor sopn) :=
  [::
    ("copy", PrimP Uptr (fun _ws sz => Ocopy sz xH));
    (* "NOP" is ignored on purpose *)
    ("mulu", PrimP Uptr (fun _ws sz => Omulu sz));
    ("adc", PrimP Uptr (fun _ws sz => Oaddcarry sz));
    ("sbb", PrimP Uptr (fun _ws sz => Osubcarry sz))
  ]%string
  ++ map (fun '(s, p) => (s, map_prim_constructor Oasm p)) prim_string.

(* used in the OCaml world, it could be a definition it seems *)
Instance asmOp_sopn : asmOp sopn :=
  { asm_op_instr := get_instr_desc;
    prim_string := sopn_prim_string }.

End ASM_OP.
