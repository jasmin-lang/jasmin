(** Transformation into the linear language *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr compiler_util.
Require Export linear.
Require Import x86_variables constant_prop.
Import Utf8 ssrZ.
Import label.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module E.

Definition pass_name := "linearization"%string.

(* FIXME: are there internal errors? *)
Definition gen_error (internal:bool) (ii:option instr_info) (msg:string) :=
  {| pel_msg      := pp_s msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := ii
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := internal
  |}.

Definition ii_error (ii:instr_info) (msg:string) :=
  gen_error false (Some ii) msg.

Definition error (msg:string) :=
  gen_error false None msg.

Definition internal_error (msg:string) :=
  gen_error true None msg.

End E.

(* --------------------------------------------------------------------------- *)
Section PROG.
Context (p:sprog) (extra_free_registers: instr_info -> option var).

(** Total size of a stack frame: local variables, extra and padding. *)
Definition stack_frame_allocation_size (e: stk_fun_extra) : Z :=
  round_ws e.(sf_align) (sf_stk_sz e + sf_stk_extra_sz e).

  Section CHECK_c.

    Context (check_i: instr -> cexec unit).

    Fixpoint check_c (c:cmd) : cexec unit :=
      match c with
      | [::] => ok tt
      | i::c => check_c c >> check_i i
      end.

  End CHECK_c.

  Section CHECK_i.

  Context (this: funname) (stack_align : wsize).

  Fixpoint check_i (i:instr) : cexec unit :=
    let (ii,ir) := i in
    match ir with
    | Cassgn x tag ty e =>
      if ty is sword sz then ok tt
      else Error (E.ii_error ii "assign not a word")
    | Copn xs tag o es =>
      ok tt
    | Cif b c1 c2 =>
      check_c check_i c1 >> check_c check_i c2
    | Cfor _ _ _ =>
      Error (E.ii_error ii "for found in linear")
    | Cwhile _ c e c' =>
      if e == Pbool false then check_c check_i c
      else check_c check_i c >> check_c check_i c'
    | Ccall _ xs fn es =>
      Let _ := assert (fn != this) (E.ii_error ii "call to self") in
      if get_fundef (p_funcs p) fn is Some fd then
        let e := f_extra fd in
        Let _ := assert match sf_return_address e with
                        | RAnone => false
                        | RAreg ra => true
                        | RAstack ofs => extra_free_registers ii != None
                        end
          (E.ii_error ii "(one_varmap) nowhere to store the return address") in
        Let _ := assert (sf_align e <= stack_align)%CMP
          (E.ii_error ii "caller need alignment greater than callee") in
        ok tt
      else Error (E.ii_error ii "call to unknown function")
    end.

  End CHECK_i.

  Let check_stack_ofs e ofs ws : bool :=
    [&&
     (sf_stk_sz e <=? ofs )%Z,
     (ofs + wsize_size ws <=? sf_stk_sz e + sf_stk_extra_sz e)%Z,
     (ws ≤ sf_align e)%CMP (* Stack frame is aligned for storing words of size ws *) &
     is_align (wrepr Uptr ofs) ws (* Stack slot is aligned *)
    ].

  Definition all_disjoint_aligned_between (lo hi: Z) (al: wsize) A (m: seq A) (slot: A → cexec (Z * wsize)) : cexec unit :=
    Let last := foldM (λ a base,
                       Let: (ofs, ws) := slot a in
                       Let _ := assert (base <=? ofs)%Z (E.error "to-save: overlap") in
                       Let _ := assert (ws ≤ al)%CMP (E.error "to-save: bad frame alignement") in
                       Let _ := assert (is_align (wrepr Uptr ofs) ws) (E.error "to-save: bad slot alignement") in
                       ok (ofs + wsize_size ws)%Z
                      ) lo m in
    assert (last <=? hi)%Z (E.error "to-save: overflow in the stack frame").

  Definition check_to_save (e: stk_fun_extra) : cexec unit :=
    if sf_return_address e is RAnone
    then
      all_disjoint_aligned_between
        (if sf_save_stack e is SavedStackStk ofs then ofs + wsize_size Uptr else sf_stk_sz e)
        (sf_stk_sz e + sf_stk_extra_sz e) U64 (sf_to_save e)
        (λ '(x, ofs), if is_word_type x.(vtype) is Some ws then ok (ofs, ws) else (Error (E.error "to-save: not a word")))
    else ok tt.

  Definition check_fd (fn: funname) (fd:sfundef) :=
    let e := fd.(f_extra) in
    let stack_align := e.(sf_align) in
    Let _ := check_c (check_i fn stack_align) fd.(f_body) in
    Let _ := check_to_save e in
    Let _ := assert [&& 0 <=? sf_stk_sz e, 0 <=? sf_stk_extra_sz e & stack_frame_allocation_size e <? wbase Uptr]%Z
                    (E.error "bad stack size") in
    Let _ := assert match sf_return_address e with
                    | RAnone => true
                    | RAreg ra => vtype ra == sword Uptr
                    | RAstack ofs => check_stack_ofs e ofs Uptr
                    end
                    (E.error "bad return-address") in
    Let _ := assert ((sf_return_address e != RAnone)
                     || match sf_save_stack e with
                        | SavedStackNone => [&& stack_align == U8, sf_stk_sz e == 0 & sf_stk_extra_sz e == 0]
                        | SavedStackReg r => (vtype r == sword Uptr) && (sf_to_save e == [::])
                        | SavedStackStk ofs => check_stack_ofs e ofs Uptr
                        end)
                    (E.error "bad save-stack") in
    ok tt.

  Definition check_prog :=
    Let _ := map_cfprog_name check_fd (p_funcs p) in
    ok tt.


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

Definition add_align ii a (lc:lcmd) :=
  match a with
  | NoAlign => lc
  | Align   =>  MkLI ii Lalign :: lc
  end.

Definition align ii a (p:label * lcmd) : label * lcmd :=
  (p.1, add_align ii a p.2).

Section FUN.

Context (fn: funname) (fn_align: wsize).

Let rsp : var := Var (sword Uptr) p.(p_extra).(sp_rsp).
Let rspi : var_i := VarI rsp xH.
Let rspg : gvar := Gvar rspi Slocal.

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
  end.

Definition linear_fd (fd: sfundef) :=
  let e := fd.(f_extra) in
  let is_export := sf_return_address e == RAnone in
  let res := if is_export then f_res fd else [::] in
  {| lfd_info := f_info fd
  ; lfd_align := sf_align e
  ; lfd_tyin := f_tyin fd
  ; lfd_arg := f_params fd
  ; lfd_tyout := f_tyout fd
  ; lfd_res := res
  ; lfd_export := is_export
  ; lfd_body :=
  let: (tail, head, lbl) :=
     match sf_return_address e with
     | RAreg r => ([:: MkLI xH (Ligoto (Pvar {| gv := VarI r xH ; gs := Slocal |})) ], [:: MkLI xH (Llabel 1) ], 2%positive)
     | RAstack z => ([:: MkLI xH (Ligoto (Pload Uptr rspi (cast_const z))) ], [:: MkLI xH (Llabel 1) ], 2%positive)
     | RAnone =>
       match sf_save_stack e with
       | SavedStackNone => ([::], [::], 1%positive)
       | SavedStackReg x =>
         let r := VarI x xH in
         ([:: MkLI xH (Lopn [:: Lvar rspi ] (Ox86 (MOV Uptr)) [:: Pvar {| gv := r ; gs := Slocal |} ]) ],
          [:: MkLI xH (Lopn [:: Lvar r ] (Ox86 (MOV Uptr)) [:: Pvar rspg ] ) ]
          ++ allocate_stack_frame false xH (sf_stk_sz e + sf_stk_extra_sz e)
          ++ [:: ensure_rsp_alignment xH e.(sf_align) ],
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
  head ++ fd'.2
  |}.

End FUN.

Definition linear_prog : cexec lprog :=
  Let _ := check_prog in
  Let _ := assert (size p.(p_globs) == 0)
             (E.internal_error "invalid p_globs") in
  let funcs := map (fun '(f,fd) => (f, linear_fd f fd)) p.(p_funcs) in
  ok {| lp_rip   := p.(p_extra).(sp_rip);
        lp_rsp   := p.(p_extra).(sp_rsp);
        lp_globs := p.(p_extra).(sp_globs);
        lp_funcs := funcs |}.

End PROG.
