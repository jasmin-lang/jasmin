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
  wsizei   : wsize;
  i_safe   : seq safe_cond;
}.

Arguments semu _ [vs vs' v] _ _.

Notation mk_instr_desc str tin i_in tout i_out semi wsizei safe:=
  {| str      := str;
     tin      := tin;
     i_in     := i_in;
     tout     := tout;
     i_out    := i_out;
     semi     := semi;
     semu     := @vuincl_app_sopn_v tin tout semi refl_equal;
     wsizei   := wsizei;
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

(*Section T.
Context {asm_op} {asmop:asmOp asm_op}.

Definition get_instr_desc o := asm_op_instr o.

Definition string_of_sopn o : string := str (get_instr_desc o) tt.

Definition sopn_tin o : list stype := tin (get_instr_desc o).
Definition sopn_tout o : list stype := tout (get_instr_desc o).
Definition sopn_sem  o := semi (get_instr_desc o).
Definition wsize_of_sopn o : wsize := wsizei (get_instr_desc o).

End T.*)

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
  (* protection for shl *)
| Oprotect  of wsize 
| Oprotect_ptr of positive 
| Oset_msf    
| Oinit_msf
| Omov_msf
| Oasm      of asm_op_t.

Definition sopn_beq (o1 o2:sopn) :=
  match o1, o2 with
  | Ocopy ws1 p1, Ocopy ws2 p2 => (ws1 == ws2) && (p1 == p2)
  | Onop, Onop => true
  | Omulu ws1, Omulu ws2 => ws1 == ws2
  | Oaddcarry ws1, Oaddcarry ws2 => ws1 == ws2
  | Osubcarry ws1, Osubcarry ws2 => ws1 == ws2
  | Oprotect ws1, Oprotect ws2 => ws1 == ws2 
  | Oprotect_ptr p1, Oprotect_ptr p2 => p1 == p2
  | Oset_msf, Oset_msf => true    
  | Oinit_msf, Oinit_msf => true
  | Omov_msf, Omov_msf => true 
  | Oasm o1, Oasm o2 => o1 == o2 ::>
  | _, _ => false
  end.

Lemma sopn_eq_axiom : Equality.axiom sopn_beq.
Proof.
  move=> [ws1 p1||ws1|ws1|ws1|ws1|p1||||o1] [ws2 p2||ws2|ws2|ws2|ws2|p2||||o2] /=;
   first (by apply (iffP andP) => [[/eqP -> /eqP ->] | [-> ->]]);
   try by (constructor || apply: reflect_inj eqP => ?? []).
Qed.

Definition sopn_eqMixin := Equality.Mixin sopn_eq_axiom.
Canonical  sopn_eqType  := EqType sopn sopn_eqMixin.

End ASM_OP.

Module Type WhichSem.
  Parameter sem_is_source: bool.
End WhichSem.

Module MkSemOp (W:WhichSem).

Section ASM_OP.

Context {pd: PointerData}.
Context `{asmop : asmOp}.


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
     wsizei   := U8; (* ??? *)
     i_safe   := [:: AllInit ws p 0];
  |}.

Definition Onop_instr := 
  mk_instr_desc (pp_s "NOP")
           [::] [::]
           [::] [::]
           (ok tt)
           U64 [::].

Definition Omulu_instr sz :=
  mk_instr_desc (pp_sz "mulu" sz)
           [:: sword sz; sword sz]
           [:: E 0; E 1] (* this info is irrelevant *)
           [:: sword sz; sword sz]
           [:: E 2; E 3] (* this info is irrelevant *)
           (fun x y => ok (@wumul sz x y)) sz [::].
 
Definition Oaddcarry_instr sz :=
  mk_instr_desc (pp_sz "adc" sz)
           [:: sword sz; sword sz; sbool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: sbool; sword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (fun x y c => let p := @waddcarry sz x y c in ok (Some p.1, p.2))
           sz [::].

Definition Osubcarry_instr sz:= 
  mk_instr_desc (pp_sz "sbb" sz)
           [:: sword sz; sword sz; sbool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: sbool; sword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (fun x y c => let p := @wsubcarry sz x y c in ok (Some p.1, p.2))
           sz [::].

Definition init_msf : exec (pointer) := 
  ok (wrepr Uptr 0).

Definition Oinit_msf_instr := 
  mk_instr_desc (pp_s "init_msf")
                [:: ]
                [:: ]
                [:: sword Uptr]
                [:: E 0]
                init_msf
                U8 (* ? *)
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
                U8 (* ? *)
                [::].

Definition protect (ws:wsize) (w:word ws) (msf:pointer) : exec (word ws) := 
  if W.sem_is_source then ok w 
  else if (msf == 0%R)%CMP then ok w 
       else if (msf == (-1)%R)%CMP 
            then let aux := (zero_extend ws msf) in ok aux
            else type_error.

(*Definition protect (ws:wsize) (w:word ws) (msf:pointer) : exec (word ws) := 
  if W.sem_is_source then ok w 
  else if (msf == 0%R)%CMP then ok w 
       else if (msf == (-1)%R)%CMP 
            then let aux := (wrepr Uptr 0) in ok (zero_extend ws aux)
            else type_error. *)

Definition Oprotect_instr (ws:wsize) := 
  mk_instr_desc (pp_sz "protect" ws)
                [:: sword ws; sword Uptr]
                [:: E 1; E 2] (* irrelevant *)
                [:: sword ws]
                [:: E 0]      (* irrelevant *)   
                (@protect ws)
                U8 (* ? *)
                [::].

(* FIX ME *)
Definition protect_ptr (p:positive) (a:WArray.array p) (msf:pointer) : exec (WArray.array p) := 
  ok a.

Lemma vuincl_protect_ptr p vs vs' v:
  List.Forall2 value_uincl vs vs' ->
  @app_sopn_v [::sarr p; sword Uptr] [::sarr p] (@protect_ptr p) vs = ok v ->
  exists2 v' : values,
   @app_sopn_v [::sarr p; sword Uptr] [::sarr p] (@protect_ptr p) vs' = ok v' &
   List.Forall2 value_uincl v v'.
Proof.
  rewrite /app_sopn_v /= => -[] {vs vs'} // v1 v2 + + hu.
  move=> [ | v1' [ | ]]; [ by t_xrbindP | | by t_xrbindP].
  move=> _ /List_Forall2_inv_l -[v2' [_ [-> [hu' /List_Forall2_inv_l ->]]]].
  t_xrbindP => /=.
  move=> t a /(value_uincl_arr hu) /= [a'] -> hut.
  move=> ? /(value_uincl_word hu') -> /= [<-] <-.
  by exists [::Varr a'] => //; constructor.
Qed.

Definition Oprotect_ptr_instr p := 
  {| str      := pp_s "protect_ptr";
     tin      := [:: sarr p; sword Uptr];
     i_in     := [:: E 1; E 2];
     tout     := [:: sarr p];
     i_out    := [:: E 0];
     semi     := @protect_ptr p;
     semu     := @vuincl_protect_ptr p;
     wsizei   := U8; (* ??? *)
     i_safe   := [:: ];
  |}.

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
                U8 (* ? *)
                [::].

Definition get_instr_desc o :=
  match o with
  | Ocopy ws p     => Ocopy_instr ws p
  | Onop           => Onop_instr
  | Omulu     sz   => Omulu_instr sz
  | Oaddcarry sz   => Oaddcarry_instr sz
  | Osubcarry sz   => Osubcarry_instr sz
  | Oprotect  sz   => Oprotect_instr sz
  | Oprotect_ptr p => Oprotect_ptr_instr p
  | Oset_msf       => Oset_msf_instr
  | Omov_msf       => Omov_msf_instr
  | Oinit_msf      => Oinit_msf_instr
  | Oasm o         => asm_op_instr o
  end.

Definition string_of_sopn o : string := str (get_instr_desc o) tt.

Definition sopn_tin o : list stype := tin (get_instr_desc o).
Definition sopn_tout o : list stype := tout (get_instr_desc o).
Definition sopn_sem  o := semi (get_instr_desc o).
Definition wsize_of_sopn o : wsize := wsizei (get_instr_desc o).

Instance eqC_sopn : eqTypeC sopn :=
  { ceqP := sopn_eq_axiom }.

Definition sopn_prim_constructor (f:asm_op -> sopn) (p : prim_constructor asm_op) : prim_constructor sopn :=
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
  ++ map (fun '(s, p) => (s, sopn_prim_constructor Oasm p)) prim_string.

(* used in the OCaml world, it could be a definition it seems *)
Instance asmOp_sopn : asmOp sopn :=
  { asm_op_instr := get_instr_desc;
    prim_string := sopn_prim_string }.

End ASM_OP.

End MkSemOp.

Module SourceSem. Definition sem_is_source := true. End SourceSem.
Module NotSourceSem. Definition sem_is_source := false. End NotSourceSem.


Module SemOp1 := MkSemOp(SourceSem).
Module SemOp2 := MkSemOp(NotSourceSem).


