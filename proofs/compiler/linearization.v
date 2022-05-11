(** Transformation into the linear language *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.
Import Relations.

Require Import expr compiler_util label constant_prop.
Require Export linear.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

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
Context {pd: PointerData}.
Context `{asmop: asmOp}.
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
    | Csyscall xs o es => 
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
        (sf_stk_sz e + sf_stk_extra_sz e) Uptr (sf_to_save e)
        (λ '(x, ofs), if is_word_type x.(vtype) is Some ws then ok (ofs, ws) else (Error (E.error "to-save: not a word")))
    else ok tt.

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

(* -------------------------------------------------------------------------- *)
(* The following are architecture-specific. *)

Record linearization_params := {
  (* Scratch register to compute addresses. *)
  lp_tmp : Ident.ident;

  (* Return a linear instruction that allocates a stack frame.
   * The linear instruction `lp_allocate_stack_frame rspi sz` increases the
   * stack pointer sz bytes.
   * In symbols, it corresponds to:
   *         R[rsp] := R[rsp] + sz
   *)
  lp_allocate_stack_frame
    : var_i      (* Variable with stack pointer register. *)
    -> Z         (* Amount of space to allocate. *)
    -> lvals * sopn * pexprs;

  (* Return a linear instruction that frees a stack frame.
   * The linear instruction `lp_free_stack_frame rspi sz` decreases the
   * stack pointer sz bytes.
   * In symbols, it corresponds to:
   *         R[rsp] := R[rsp] - sz
   *)
  lp_free_stack_frame
    : var_i      (* Variable with stack pointer register. *)
    -> Z         (* Amount of space to free. *)
    -> lvals * sopn * pexprs;

  (* Return a linear instruction that ensures the stack pointer is aligned.
   * The linear instruction `lp_ensure_rsp_alignment rspi ws` ensures that
   * the k least significant bits of the stack pointer are 0, where k is the
   * size of ws in bytes.
   * In symbols, it corresponds to:
   *         R[rsp] := R[rsp] & - wsize_size ws
   * where rsp is the stack pointer register.
   *)
  lp_ensure_rsp_alignment
    : var_i      (* Variable with stack pointer register. *)
    -> wsize     (* Size of the unit to align to. *)
    -> lvals * sopn * pexprs;

  (* Return a linear instruction that corresponds to assignment.
   * In symbols, the linear instruction `lp_lassign x ws e` corresponds to
   *         x := (ws)e
   *)
  lp_lassign
    : lval       (* Value to overwrite. *)
    -> wsize     (* Size of the value to assign. *)
    -> pexpr     (* Value to assign. *)
    -> lvals * sopn * pexprs;
}.

(* -------------------------------------------------------------------------- *)

Context (lp: linearization_params) (fn: funname) (fn_align: wsize).

Let rsp : var := Var (sword Uptr) p.(p_extra).(sp_rsp).
Let rspi : var_i := VarI rsp xH.
Let rspg : gvar := Gvar rspi Slocal.
Let var_tmp : var := Var (sword Uptr) lp.(lp_tmp).

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
                      | SavedStackNone => [&& sf_to_save e == [::], stack_align == U8, sf_stk_sz e == 0 & sf_stk_extra_sz e == 0]
                      | SavedStackReg r => [&& vtype r == sword Uptr & sf_to_save e == [::] ]
                      | SavedStackStk ofs => [&& check_stack_ofs e ofs Uptr & ~~ Sv.mem var_tmp (sv_of_list fst (sf_to_save e)) ]
                      end)
                  (E.error "bad save-stack") in
  ok tt.

Definition check_prog :=
  Let _ := map_cfprog_name check_fd (p_funcs p) in
  ok tt.

(* We use projections instead of destructuring let to avoid blocking reductions. *)
Definition lassign ii x ws e : linstr :=
  let args := lp.(lp_lassign) x ws e in
  MkLI ii (Lopn args.1.1 args.1.2 args.2).

(* Return a linear instruction that corresponds to copying a register.
 * The linear instruction `lmove ii rd ws r0` corresponds to
 *         R[rd] := (ws)R[r0]
 *)
Definition lmove
  (ii: instr_info) (* Instruction information. *)
  (rd: var_i)      (* Destination register. *)
  (ws: wsize)      (* Size of the value to copy. *)
  (r0: gvar)       (* Source register. *)
  : linstr :=
  lassign ii (Lvar rd) ws (Pvar r0).

(* Return a linear instruction that corresponds to loading from memory.
 * The linear instruction `lload ii rd ws r0 ofs` corresponds to
 *         R[rd] := (ws)M[R[r0] + ofs]
 *)
Definition lload
  (ii: instr_info) (* Instruction information. *)
  (rd: var_i)      (* Destination register. *)
  (ws: wsize)      (* Size of the value to copy. *)
  (r0: var_i)      (* Base register. *)
  (ofs: Z)         (* Offset. *)
  : linstr :=
  lassign ii (Lvar rd) ws (Pload ws r0 (cast_const ofs)).

(* Return a linear instruction that corresponds to storing to memory.
 * The linear instruction `lstore ii rd ofs ws r0` corresponds to
 *         M[R[rd] + ofs] := (ws)R[r0]
 *)
Definition lstore
  (ii: instr_info) (* Instruction information. *)
  (rd: var_i)      (* Base register. *)
  (ofs: Z)         (* Offset. *)
  (ws: wsize)      (* Size of the value to copy. *)
  (r0: gvar)       (* Source register. *)
  : linstr :=
  lassign ii (Lmem ws rd (cast_const ofs)) ws (Pvar r0).

Definition allocate_stack_frame (free: bool) (ii: instr_info) (sz: Z) : lcmd :=
  if sz == 0%Z
  then [::]
  else let args := if free
                   then lp.(lp_allocate_stack_frame) rspi sz
                   else lp.(lp_free_stack_frame) rspi sz
       in [:: MkLI ii (Lopn args.1.1 args.1.2 args.2) ].

Definition ensure_rsp_alignment ii (al: wsize) : linstr :=
  let args := lp.(lp_ensure_rsp_alignment) rspi al in
  MkLI ii (Lopn args.1.1 args.1.2 args.2).

(* Return a linear command that pushes variables to the stack.
 * The linear command `lp_push_to_save ii to_save` pushes each
 * variable x to the stack with an offset o for each (x, o) in to_save.
 * The variables in to_save are all words.
 * In symbols, it corresponds to:
 *         M[R[rsp] + o] := x
 * for each (x, o) in to_save.
 *)
Definition push_to_save
  (ii: instr_info)         (* Instruction information for the command. *)
  (to_save: seq (var * Z)) (* Variables to save and offsets in the stack. *)
  : lcmd :=
  let mkli '(x, ofs) :=
    if is_word_type x.(vtype) is Some ws
    then lstore ii rspi ofs ws {| gv := VarI x xH; gs := Slocal; |}
    else MkLI ii Lalign (* Absurd case. *)
  in List.map mkli to_save.

(* Return a linear command that loads variables from the stack.
 * The linear command `lp_pop_to_save ii to_save` loads each
 * variable x from the stack with an offset o for each (x, o) in to_save.
 * The variables in to_save are all words.
 * In symbols, it corresponds to:
 *         x := M[R[rsp] + o]
 * for each (x, o) in to_save.
 *)
Definition pop_to_save
  (ii: instr_info)         (* Instruction information for the command. *)
  (to_save: seq (var * Z)) (* Variables to load and offsets in the stack. *)
  : lcmd :=
  let mkli '(x, ofs) :=
    if is_word_type x.(vtype) is Some ws
    then lload ii (VarI x xH) ws rspi ofs
    else MkLI ii Lalign (* Absurd case. *)
  in List.map mkli to_save.

Fixpoint linear_i (i:instr) (lbl:label) (lc:lcmd) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn x _ ty e =>
    let lc' := if ty is sword sz
               then lassign ii x sz e :: lc
               else lc
    in (lbl, lc')

  | Copn xs _ o es => (lbl, MkLI ii (Lopn xs o es) :: lc)

  | Csyscall xs o es => (lbl, MkLI ii (Lsyscall o) :: lc)

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
        let lcall := (fn', if fn' == fn
                           then lret    (* Absurd case. *)
                           else xH      (* Entry point. *)
                     ) in
        match sf_return_address e with
        | RAreg ra =>
          (* Save return address to register ra.
           * 1. Allocate stack frame.
           * 2. Store return label in ra.
           * 3. Insert jump to callee.
           * 4. Insert return label (callee will jump back here).
           * 5. Free stack frame.
           * 6. Continue.
           *)
          (lbl, before
                  ++ MkLI ii (LstoreLabel (Lvar (VarI ra xH)) lret)
                  :: MkLI ii (Lgoto lcall)
                  :: MkLI ii (Llabel lret)
                  :: after
                  ++ lc
          )

        | RAstack z =>
          (* Save return address to the stack with an offset.
           * 1. Allocate stack frame.
           * 2. Store return label in ra.
           * 3. Push ra to stack.
           * 4. Insert jump to callee.
           * 5. Insert return label (callee will jump back here).
           * 6. Free stack frame.
           * 7. Continue.
           *)
          if extra_free_registers ii is Some ra
          then let glob_ra := Gvar (VarI ra xH) Slocal in
               (lbl, before
                       ++ MkLI ii (LstoreLabel (Lvar (VarI ra xH)) lret)
                       :: lstore ii rspi z Uptr glob_ra
                       :: MkLI ii (Lgoto lcall)
                       :: MkLI ii (Llabel lret)
                       :: after
                       ++ lc
               )
          else (lbl, lc)
        | RAnone => (lbl, lc)
        end
    else (lbl, lc )
  | Cfor _ _ _ => (lbl, lc)
  end.

Definition linear_body (e: stk_fun_extra) (body: cmd) : lcmd :=
  let: (tail, head, lbl) :=
     match sf_return_address e with
     | RAreg r =>
       ( [:: MkLI xH (Ligoto (Pvar (Gvar (VarI r xH) Slocal))) ]
       , [:: MkLI xH (Llabel 1) ]
       , 2%positive
       )
     | RAstack z =>
       ( [:: MkLI xH (Ligoto (Pload Uptr rspi (cast_const z))) ]
       , [:: MkLI xH (Llabel 1) ]
       , 2%positive
       )
     | RAnone =>
       match sf_save_stack e with
       | SavedStackNone =>
         ([::], [::], 1%positive)
       | SavedStackReg x =>
         (* Tail: R[rsp] := R[x]
          * Head: R[x] := R[rsp]
          *       Setup stack.
          *)
         let r := VarI x xH in
         ( [:: lmove xH rspi Uptr (Gvar r Slocal) ]
         , lmove xH r Uptr rspg
             :: allocate_stack_frame false xH (sf_stk_sz e + sf_stk_extra_sz e)
             ++ [:: ensure_rsp_alignment xH e.(sf_align) ]
         , 1%positive
         )
       | SavedStackStk ofs =>
         (* Tail: Load saved registers.
          *       R[rsp] := M[R[rsp] + ofs]
          * Head: R[r] := R[rsp]
          *       Setup stack.
          *       M[R[rsp] + ofs] := R[r]
          *       Push registers to save to the stack.
          *)
         let tmp := VarI var_tmp xH in
         ( pop_to_save xH e.(sf_to_save)
             ++ [:: lload xH rspi Uptr rspi ofs ]
         , lmove xH tmp Uptr rspg
             :: allocate_stack_frame false xH (sf_stk_sz e + sf_stk_extra_sz e)
             ++ ensure_rsp_alignment xH e.(sf_align)
             :: lstore xH rspi ofs Uptr (Gvar tmp Slocal)
             :: push_to_save xH e.(sf_to_save)
         , 1%positive)
       end
     end
  in
  let fd' := linear_c linear_i body lbl tail in
  head ++ fd'.2.

Definition linear_fd (fd: sfundef) :=
  let e := fd.(f_extra) in
  let is_export := sf_return_address e == RAnone in
  let res := if is_export then f_res fd else [::] in
  {| lfd_info := f_info fd
  ; lfd_align := sf_align e
  ; lfd_tyin := f_tyin fd
  ; lfd_arg := f_params fd
  ; lfd_tyout := f_tyout fd
  ; lfd_total_stack := sf_stk_max e
  ; lfd_res := res
  ; lfd_export := is_export
  ; lfd_callee_saved := if is_export then map fst e.(sf_to_save) else [::]
  ; lfd_body := linear_body e fd.(f_body)
  |}.

End FUN.

Definition linear_prog (lparams: linearization_params) : cexec lprog :=
  Let _ := check_prog lparams in
  Let _ := assert (size p.(p_globs) == 0)
             (E.internal_error "invalid p_globs") in
  let funcs := map (fun '(f,fd) => (f, linear_fd lparams f fd)) p.(p_funcs) in
  ok {| lp_rip   := p.(p_extra).(sp_rip);
        lp_rsp   := p.(p_extra).(sp_rsp);
        lp_globs := p.(p_extra).(sp_globs);
        lp_funcs := funcs |}.

End PROG.
