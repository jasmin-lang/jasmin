(** Transformation into the linear language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From Coq Require Import ZArith Utf8.
Import Relations.

Require Import expr fexpr compiler_util label constant_prop.
Require Export linear linear_util.
Import word_ssrZ.

Local Open Scope seq_scope.

Module E.

Definition pass_name := "linearization"%string.

Definition my_error (msg:pp_error) :=
  {| pel_msg      := msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := None
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := false
  |}.

(* FIXME: are there internal errors? *)
Definition gen_error (internal: bool) (ii: option instr_info) (msg: pp_error) :=
  {| pel_msg      := msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := ii
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := internal
  |}.

Definition ii_error (ii: instr_info) (msg: string) :=
  gen_error false (Some ii) (pp_s msg).

Definition error (msg: string) :=
  gen_error false None (pp_s msg).

Definition internal_error (msg: string) :=
  gen_error true None (pp_s msg).

Definition assign_remains (ii : instr_info) (lv: lval) (e: pexpr) :=
  gen_error false (Some ii)
    (pp_nobox [:: pp_s "The following assignment remains:"; PPEbreak;
      pp_lv lv; pp_s " = "; pp_e e; PPEbreak;
      pp_s "Is there an instruction in the target architecture that can implement it?"; PPEbreak;
      pp_s "More information may be found online: https://jasmin-lang.readthedocs.io/en/latest/misc/faq.html#linearization"
  ]).

End E.


(* --------------------------------------------------------------------------- *)

Record linearization_params {asm_op : Type} {asmop : asmOp asm_op} :=
  {
    (* Scratch registers used to set up stack. *)
    lip_tmp  : Ident.ident;
    lip_tmp2 : Ident.ident;

    (* Variables that can't be used to save the stack pointer.
       If lip_set_up_sp_register uses its auxiliary argument,
       it should contain lip_tmp.
    *)
    lip_not_saved_stack : seq Ident.ident;

    (* Return the arguments for a linear instruction that allocates a stack
       frame.
       The linear instruction derived from [lip_allocate_stack_frame rspi sz]
       decreases the stack pointer [sz] bytes.
       In symbols, it corresponds to:
               R[rsp] := R[rsp] - sz
     *)
    lip_allocate_stack_frame :
      var_i    (* Variable with stack pointer register. *)
      -> option var_i (* An auxiliary variable *)
      -> Z     (* Amount of space to allocate. *)
      -> seq fopn_args;

    (* Return the arguments for a linear instruction that frees a stack frame.
       The linear instruction derived from [lip_free_stack_frame rspi sz]
       increases the stack pointer [sz] bytes.
       In symbols, it corresponds to:
               R[rsp] := R[rsp] + sz
     *)
    lip_free_stack_frame :
      var_i    (* Variable with stack pointer register. *)
      -> option var_i (* An auxiliary variable *)
      -> Z     (* Amount of space to free. *)
      -> seq fopn_args;

    (* Return the arguments for a linear command that saves the value of the
       stack pointer to a register, allocates a stack frame and aligns the stack
       pointer.
       The linear command derived from [lip_set_up_sp_register rspi sz ws r]
       corresponds to:
               r := R[rsp]
               R[rsp] := (R[rsp] - sz) & - wsize_size ws
    *)
    lip_set_up_sp_register :
      var_i    (* Variable with stack pointer register. *)
      -> Z     (* Size of the stack frame to allocate. *)
      -> wsize (* Alignment. *)
      -> var_i (* Variable to save stack pointer to. *)
      -> var_i (* An auxiliary variable *)
      -> seq fopn_args;

    (* Return the arguments for a linear instruction that corresponds to
       a move between two registers.
       In symbols, the linear instruction derived from [lip_lmove xd xs]
       corresponds to:
               xd := (Uptr)xs
     *)
    lip_lmove :
      var_i       (* Destination variable. *)
      -> var_i    (* Source variable. *)
      -> fopn_args;

    (* Check if the given size can be written to/read from memory,
       i.e if an operation exists for that size. *)
    lip_check_ws : wsize -> bool;

    (* Return the arguments for a linear instruction that corresponds to
       a store to memory.
       In symbols, the linear instruction derived from [lip_lstore xd ofs xs]
       corresponds to:
               [xd + ofs] := xs
     *)
    lip_lstore :
      var_i        (* Base register. *)
      -> Z         (* Offset. *)
      -> var_i     (* Source register. *)
      -> fopn_args;

    (* Return the arguments for a linear instruction that corresponds to
       a load from memory.
       In symbols, the linear instruction derived from [lip_lload xd xs ofs]
       corresponds to:
               xd = [xs + ofs]
     *)
    lip_lload :
      var_i        (* Destination register. *)
      -> var_i     (* Base register. *)
      -> Z         (* Offset. *)
      -> fopn_args;

    (* Push variables to the stack at the given offset *)
    lip_lstores :
      var_i              (* The current stack pointer *)
      -> seq (var * Z)   (* The list of variables to save at a given offset *)
      -> seq fopn_args;

    (* Load variables from the stack at the given offset *)
    lip_lloads:
      var_i           (* The current stack pointer *)
      -> seq (var * Z)   (* The list of variables to restore from a given offset *)
      -> Z            (* The offset for the stack pointer to restore*)
      -> seq fopn_args;
  }.

(* Note on function calls:

   + For X86:

     - Return address passed by register in ra:
          LstoreLabel ra lret
          Lgoto lcall
          Llabel lret
       Internally (to the callee), ra needs to be free.
       The return is implemented by
          Ligoto ra
       /!\ For protection against Spectre we should avoid this calling convention

     - Return address passed by stack (on top of the stack):
          Lcall None lcall;
          Llabel lret;
       The return is implemented by
          Lret  (i.e ret in X86)
        The stack frame is incremented by the caller and by the call instruction (to push ra).


   + For ARM v7:

     - Return address passed by register in ra
         Lcall (Some ra) lcall (i.e BL lcall with the constraint that ra should be LR (r14))
         Llabel lret
       Internally (to the callee), ra needs to be free.
       The return is implemented by
          Ligoto ra   (i.e BX ra)
       The stack frame is incremented by the caller.


     - Return address passed by stack (on top of the stack):
         Lcall (Some ra) lcall (i.e BL lcall with the constraint that ra should be LR (r14))
         Llabel lret
       ra needs to be free when Lcall is executed.
       The first instruction of the function call needs to push ra.
         store sp ra
       So ra needs to be known at call site and at the entry of the function.
       The stack frame is incremented by the caller.

       The return is implemented by
         Lret (i.e POP PC in arm v7)


   + For RISC-V:

     - Return address passed by register in r
         Lcall (Some r) lcall (i.e call lcall with the constraint that r should be ra (x1))
         Llabel lret
       Internally (to the callee), r needs to be free.
       The return is implemented by
          Ligoto r (i.e jr r, also written ret if r is ra)
       The stack frame is incremented by the caller.

     - Return address passed by stack (on top of the stack):
         Lcall (Some ra_call) lcall (i.e call lcall with the constraint that ra_call should be ra (x1))
         Llabel lret
       ra_call needs to be free when Lcall is executed.
       The first instruction of the function call needs to push ra_call.
         store sp ra_call
       So ra_call needs to be known at call site and at the entry of the function.
       The stack frame is incremented by the caller.

       The return is implemented by
         load ra_return sp
         Ligoto ra_return (i.e. jr ra_return, also written ret if ra_return is ra)
       ra_return needs to be free at the end of the callee (in particular, it cannot
       be a result).
*)

(* The following functions are defined here, so that they can be shared between
   the architectures. The proofs are shared too (see linearization_proof.v).

   An architecture can define its own functions when there is something more
   efficient to do, and rely on one of these implementations in the default case. *)
Section DEFAULT.
Context {asm_op : Type} {pd : PointerData} {asmop : asmOp asm_op}.
Context (lip_tmp2 : Ident.ident).
Context (lip_lstore  : var_i -> Z -> var_i -> fopn_args)
        (lip_lload   : var_i -> var_i -> Z -> fopn_args)
        (lip_add_imm : var_i -> var_i -> Z -> seq fopn_args)
        (lip_imm_small : Z -> bool).

Definition lstores_dfl (rsp: var_i) (to_save : seq (var * Z)) :=
  map (fun '(x,ofs) => lip_lstore rsp ofs (VarI x dummy_var_info)) to_save.

Definition lstores_imm_dfl (rsp : var_i) (to_save : seq (var * Z)) :=
  if all (fun '(_,ofs) => lip_imm_small ofs) to_save then
    lstores_dfl rsp to_save
  else
    let ofs0 := snd (head (v_var rsp, 0%Z) to_save) in
    let tmp2 := VarI {| vtype := sword Uptr; vname := lip_tmp2 |} dummy_var_info in
    let to_save := map (fun '(x, ofs) => (x, ofs - ofs0)%Z) to_save in
    lip_add_imm tmp2 rsp ofs0 ++ lstores_dfl tmp2 to_save.

Definition lloads_aux (rsp:var_i) (to_restore : seq (var * Z)) :=
  map (fun '(x, ofs) => lip_lload (VarI x dummy_var_info) rsp ofs) to_restore.

Definition lloads_dfl (rsp:var_i) (to_restore : seq (var * Z)) (spofs:Z) :=
  lloads_aux rsp (to_restore ++ [:: (v_var rsp, spofs)]).

Definition lloads_imm_dfl (rsp:var_i) (to_restore : seq (var * Z)) (spofs:Z) :=
  let to_restore := to_restore ++ [:: (v_var rsp, spofs)] in
  if all (fun '(_,ofs) => lip_imm_small ofs) to_restore then
    lloads_aux rsp to_restore
  else
    let ofs0 := snd (head (v_var rsp, 0%Z) to_restore) in
    let tmp2 := VarI {| vtype := sword Uptr; vname := lip_tmp2 |} dummy_var_info in
    let to_restore := map (fun '(x, ofs) => (x, ofs - ofs0)%Z) to_restore in
    lip_add_imm tmp2 rsp ofs0 ++ lloads_aux tmp2 to_restore.

End DEFAULT.

Section WITH_PARAMS.

Context
  {asm_op : Type}
  {pd : PointerData}
  {asmop : asmOp asm_op}
  (liparams : linearization_params).

(* Return a linear instruction that corresponds to copying a register.
   The linear instruction [lmove rd rs] corresponds to
           R[rd] := (Uptr)R[rs]
 *)
Definition lmove
  (ii: instr_info)
  (rd : var_i)      (* Destination register. *)
  (rs : var_i)       (* Source register. *)
  : linstr :=
  li_of_fopn_args ii (lip_lmove liparams rd rs).

(* Return a linear instruction that corresponds to loading from memory.
   The linear instruction [lload rd rs ofs] corresponds to
           R[rd] := M[R[rs] + ofs]
 *)
Definition lload
  (ii: instr_info)
  (rd : var_i) (* Destination register. *)
  (rs : var_i) (* Base register. *)
  (ofs : Z)    (* Offset. *)
  : linstr :=
  li_of_fopn_args ii (lip_lload liparams rd rs ofs).

(* Return a linear instruction that corresponds to storing to memory.
   The linear instruction [lstore rd ofs rs] corresponds to
           M[R[rd] + ofs] := R[rs]
 *)
Definition lstore
  (ii: instr_info)
  (rd : var_i)      (* Base register. *)
  (ofs : Z)         (* Offset. *)
  (rs : var_i)      (* Source register. *)
  : linstr :=
  li_of_fopn_args ii (lip_lstore liparams rd ofs rs).

Definition set_up_sp_register
  (ii: instr_info)
  (vrspi : var_i) (sf_sz : Z) (al : wsize) (r : var_i) (tmp : var_i) : lcmd :=
  map (li_of_fopn_args ii) (lip_set_up_sp_register liparams vrspi sf_sz al r tmp).

(* -------------------------------------------------------------------------- *)
Section CHECK_SOME.
  Context (E: Type) (error: string → E) (A B: Type) (conv: A → option B).

  Definition check_Some msg (a: A) : result E unit :=
    assert (isSome (conv a)) (error msg).

End CHECK_SOME.

(* -------------------------------------------------------------------------- *)
Section EXPR.
  Context (ii: instr_info).

  Definition to_fexpr (e: pexpr) : fexpr :=
    if fexpr_of_pexpr e is Some r then r else Fconst 0.

  Let error msg := E.gen_error true (Some ii) (pp_s msg).

  Definition check_fexpr := check_Some error fexpr_of_pexpr "check_fexpr".

  Definition check_rexpr := check_Some error rexpr_of_pexpr "check_rexpr".

  Definition check_lexpr := check_Some error lexpr_of_lval "check_lexpr".

End EXPR.

Definition ovar_of_ra (ra : return_address_location) : option var :=
  match ra with
  | RAreg ra _ => Some ra
  | RAstack ra_call _ _ _ => ra_call
  | RAnone => None
  end.

Definition ovari_of_ra (ra : return_address_location) : option var_i :=
  omap mk_var_i (ovar_of_ra ra).

Definition tmp_of_ra (ra : return_address_location) : option var :=
  match ra with
  | RAreg _ o => o
  | RAstack _ _ _ o => o
  | RAnone => None
  end.

Definition tmpi_of_ra (ra : return_address_location) : option var_i :=
  omap mk_var_i (tmp_of_ra ra).

Section PROG.

Context
  (p : sprog).
(*  (extra_free_registers : instr_info -> option var) *)

Notation rsp := {| vtype := sword Uptr; vname := sp_rsp (p_extra p); |}.
Notation rspi := (mk_var_i rsp).

Notation var_tmp  := {| vtype := sword Uptr; vname := lip_tmp  liparams; |}.
Notation var_tmp2 := {| vtype := sword Uptr; vname := lip_tmp2 liparams; |}.

(** Total size of a stack frame: local variables, extra and padding. *)
Definition stack_frame_allocation_size (e: stk_fun_extra) : Z :=
  round_ws e.(sf_align) (sf_stk_sz e + sf_stk_extra_sz e).

Definition frame_size (e: stk_fun_extra) : Z :=
  if is_RAnone e.(sf_return_address) then
    (sf_stk_sz e + sf_stk_extra_sz e)%Z
  else
    stack_frame_allocation_size e.

(* Return a linear command that pushes variables to the stack.
 * The linear command `lp_push_to_save ii to_save` pushes each
 * variable x to the stack with an offset o for each (x, o) in to_save.
 * The variables in to_save are all words.
 * In symbols, it corresponds to:
 *         M[R[rsp] + o] := x
 * for each (x, o) in to_save.
 *)
Definition push_to_save
  (ii: instr_info)
  (to_save: seq (var * Z)) (* Variables to save and offsets in the stack. *)
  (sp : var * Z)           (* Variable to save containing the initial value of sp *)
  : lcmd :=
  map (li_of_fopn_args ii)
      (lip_lstores liparams rspi (to_save ++ [::sp])).

(* Return a linear command that loads variables from the stack.
 * The linear command `lp_pop_to_save ii to_save` loads each
 * variable x from the stack with an offset o for each (x, o) in to_save.
 * The variables in to_save are all words.
 * In symbols, it corresponds to:
 *         x := M[R[rsp] + o]
 * for each (x, o) in to_save.
 *)
Definition pop_to_save
  (ii: instr_info)
  (to_save: seq (var * Z)) (* Variables to load and offsets in the stack. *)
  (sp : Z)                 (* Offset for restoring the stack pointer *)
  : lcmd :=
  map (li_of_fopn_args ii)
      (lip_lloads liparams rspi to_save sp).

  Section CHECK_c.

    Context (check_i: instr -> cexec unit).

    Fixpoint check_c (c:cmd) : cexec unit :=
      match c with
      | [::] => ok tt
      | i::c => check_c c >> check_i i
      end.

  End CHECK_c.

  Section CHECK_i.

  Context (this: funname) (e_caller : stk_fun_extra).

  Fixpoint check_i (i:instr) : cexec unit :=
    let (ii,ir) := i in
    match ir with
    | Cassgn lv _ _ e => Error (E.assign_remains ii lv e)
    | Copn xs tag o es =>
      allM (check_rexpr ii) es >> allM (check_lexpr ii) xs
    | Csyscall xs o es =>
      ok tt
    | Cif b c1 c2 =>
      check_fexpr ii b >> check_c check_i c1 >> check_c check_i c2
    | Cfor _ _ _ =>
      Error (E.ii_error ii "for found in linear")
    | Cwhile _ c e _ c' =>
      match is_bool e with
      | Some false => check_c check_i c
      | Some true => check_c check_i c >> check_c check_i c'
      | None => check_fexpr ii e >> check_c check_i c >> check_c check_i c'
      end
    | Ccall xs fn es =>
      Let _ := assert (fn != this) (E.ii_error ii "call to self") in
      if get_fundef (p_funcs p) fn is Some fd then
        let e := f_extra fd in
        Let _ := assert (~~ is_RAnone (sf_return_address e))
          (E.ii_error ii "internal call to an export function") in
        Let _ := assert (sf_align e <= sf_align e_caller)%CMP
          (E.ii_error ii "caller need alignment greater than callee") in
        Let _ := assert (sf_stk_max e + frame_size e_caller <=? sf_stk_max e_caller)%Z
          (E.ii_error ii "max size problem") in
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

  Let check_stack_ofs_internal_call e ofs ws : bool :=
    [&&
     ofs == 0%Z,
     wsize_size ws == sf_stk_ioff e &
     (ws ≤ sf_align e)%CMP (* Stack frame is aligned for storing words of size ws *)
    ].

  Definition check_to_save_slot (p : var * Z) : cexec (Z * wsize) :=
    let '(x, ofs) := p in
    if is_word_type (vtype x) is Some ws
    then ok (ofs, ws)
    else
      Error (E.error "to-save: not a word").

  Definition all_disjoint_aligned_between (lo hi: Z) (al: wsize) (m: seq (var * Z)) : cexec unit :=
    Let last := foldM (λ a base,
                       Let: (ofs, ws) := check_to_save_slot a in
                       Let _ := assert (base <=? ofs)%Z (E.my_error (pp_hov [::pp_s "to-save: overlap"; pp_e (Pconst base); pp_e (Pconst ofs)])) in
                       Let _ := assert (ws ≤ al)%CMP (E.error "to-save: bad frame alignement") in
                       Let _ := assert (is_align (wrepr Uptr ofs) ws) (E.error "to-save: bad slot alignement") in
                       Let _ := assert (lip_check_ws liparams ws) (E.error "to-save: bad wsize") in
                       ok (ofs + wsize_size ws)%Z
                      ) lo m in
    assert (last <=? hi)%Z (E.error "to-save: overflow in the stack frame").

  Definition check_to_save (e: stk_fun_extra) : cexec unit :=
    if is_RAnone (sf_return_address e)
    then
      (* FIXME: this assert seems redundant with the check in check_fd *)
      let stk_size := (sf_stk_sz e + sf_stk_extra_sz e)%Z in
      Let _ := assert (if sf_save_stack e is SavedStackStk ofs then (ofs + wsize_size Uptr <=? stk_size)%Z else true)
                      (E.error "stack size to small") in

      all_disjoint_aligned_between
        (sf_stk_sz e)
        (if sf_save_stack e is SavedStackStk ofs then ofs else (sf_stk_sz e + sf_stk_extra_sz e))
        e.(sf_align) (sf_to_save e)
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


Section LINEAR_END_C.

  Variable linear_end_i : funname -> instr -> nat -> nat.

  Fixpoint linear_end_c (fn: funname) (c0: cmd) (n0: nat) :
    nat :=
    match c0 with
    | [::] => n0
    | i::c =>
        let n1 := linear_end_i fn i n0 in
        linear_end_c fn c n1 
    end.

End LINEAR_END_C.


Section LINEAR_FULL_C.

  Variable linear_full_i :
    funname -> instr -> nat -> label -> nat * label * lcmd.

  Fixpoint linear_full_c (fn: funname) (c0: cmd) (n0: nat) (lbl0:label) :
    nat * label * lcmd :=
    match c0 with
    | [::] => (n0, lbl0, nil)
    | i::c =>
        let '(n1, lbl1, c1) := linear_full_i fn i n0 lbl0 in
        linear_full_c fn c n1 lbl1
    end.

End LINEAR_FULL_C.


Definition add_align ii a (lc:lcmd) :=
  match a with
  | NoAlign => lc
  | Align   =>  MkLI ii Lalign :: lc
  end.

Definition align ii a (p:label * lcmd) : label * lcmd :=
  (p.1, add_align ii a p.2).


Section FUN.

Context
  (fn : funname).

Definition ov_type_ptr (o: option var) :=
   if o is Some r then vtype r == sword Uptr else true.

Definition check_fd (fn: funname) (fd:sfundef) :=
  let e := fd.(f_extra) in
  let stack_align := e.(sf_align) in
  Let _ := check_c (check_i fn e) fd.(f_body) in
  Let _ := check_to_save e in
  (* FIXME: strange to have both stack_frame_allocation_size and frame_size *)
  Let _ := assert [&& 0 <=? sf_stk_sz e,
                      0 <=? sf_stk_extra_sz e,
                      stack_frame_allocation_size e <? wbase Uptr
                    & frame_size e <=? sf_stk_max e]%Z
                  (E.error "bad stack size") in
  Let _ := assert match sf_return_address e with
                  | RAnone => ~~ (var_tmp2 \in map v_var fd.(f_res))
                  | RAreg ra tmp => (vtype ra == sword Uptr) && ov_type_ptr tmp
                  | RAstack ra_call ra_return ofs tmp =>
                      [&& ov_type_ptr ra_call
                        , ov_type_ptr ra_return
                        , ov_type_ptr tmp
                        & check_stack_ofs_internal_call e ofs Uptr]
                  end
                  (E.error "bad return-address") in
  let ok_save_stack :=
    let sf_sz := (sf_stk_sz e + sf_stk_extra_sz e)%Z in
    match sf_save_stack e with
    | SavedStackNone =>
        [&& sf_to_save e == [::]
          , sf_align e == U8
          , sf_stk_sz e == 0%Z
          & sf_stk_extra_sz e == 0%Z
        ]

    | SavedStackReg x =>
        [&& vtype x == sword Uptr
          , sf_to_save e == [::]
          & vname x != lip_tmp liparams
        ]

    | SavedStackStk ofs =>
        [&& check_stack_ofs e ofs Uptr
          , ~~ Sv.mem var_tmp  (sv_of_list fst (sf_to_save e))
          , ~~ Sv.mem var_tmp2 (sv_of_list fst (sf_to_save e))
          & ~~ Sv.mem rsp (sv_of_list fst (sf_to_save e))
          ]
    end
  in
  Let _ :=
    assert
      (~~ is_RAnone (sf_return_address e) || ok_save_stack)
      (E.error "bad save-stack")
  in
  ok tt.

Definition check_prog :=
  Let _ := map_cfprog_name check_fd (p_funcs p) in
  ok tt.

Definition allocate_stack_frame (free: bool) (ii: instr_info) (sz: Z) (tmp: option var_i)
(rastack: bool) : lcmd :=
  let sz := if rastack then (sz - wsize_size Uptr)%Z else sz in
  if sz == 0%Z
  then [::]
  else
    let args := if free
                   then (lip_free_stack_frame liparams) rspi tmp sz
                   else (lip_allocate_stack_frame liparams) rspi tmp sz in
     map (li_of_fopn_args ii) args.

Definition is_RAstack_None_call ra :=
  if ra is RAstack None _ _ _ then true else false.

Definition is_RAstack_None_return ra :=
  if ra is RAstack _ None _ _ then true else false.

Let ReturnTarget := Llabel ExternalLabel.
Let Llabel := linear.Llabel InternalLabel.

Fixpoint linear_i (i:instr) (lbl:label) (lc:lcmd) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ _ => (lbl, lc) (* absurd case *)

  | Copn xs _ o es =>
      match oseq.omap lexpr_of_lval xs, oseq.omap rexpr_of_pexpr es with
      | Some xs, Some es => (lbl, MkLI ii (Lopn xs o es) :: lc)
      | _, _ => (lbl, lc) (* absurd case *)
      end

  | Csyscall xs o es => (lbl, MkLI ii (Lsyscall o) :: lc)

  | Cif e [::] c2 =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond (to_fexpr e) L1) >;
      linear_c linear_i c2 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 [::] =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond (to_fexpr (snot e)) L1) >;
      linear_c linear_i c1 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 c2 =>
    let L1 := lbl in
    let L2 := next_lbl L1 in
    let lbl := next_lbl L2 in
                           MkLI ii (Lcond (to_fexpr e) L1) >;
                           linear_c linear_i c2 ;;
                           MkLI ii (Lgoto (fn, L2)) >;
    MkLI ii (Llabel L1) >; linear_c linear_i c1 lbl
   (MkLI ii (Llabel L2) :: lc)

  | Cwhile a c e _ c' =>
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
                             (MkLI ii (Lcond (to_fexpr e) L1) :: lc))
      | _ =>
      let L1 := lbl in
      let L2 := next_lbl L1 in
      let lbl := next_lbl L2 in
                             MkLI ii (Lgoto (fn, L1)) >;
      align ii a (MkLI ii (Llabel L2) >; linear_c linear_i c' ;;
      MkLI ii (Llabel L1) >; linear_c linear_i c lbl
                             (MkLI ii (Lcond (to_fexpr e) L2) :: lc))
      end
    end

  | Ccall xs fn' es =>
    if get_fundef (p_funcs p) fn' is Some fd then
      let e := f_extra fd in
      let ra := sf_return_address e in
      if is_RAnone ra then (lbl, lc)
      else
        let sz := stack_frame_allocation_size e in
        let tmp := tmpi_of_ra ra in
        let Before := allocate_stack_frame false ii sz tmp
                        (is_RAstack_None_call ra) in
        let After := allocate_stack_frame true ii sz tmp
                        (is_RAstack_None_return ra) in
        let lret := lbl in
        let lbl := next_lbl lbl in
        (* The test is used for the proof of linear_has_valid_labels *)
        let lcall := (fn', if fn' == fn
                           then lret    (* Absurd case. *)
                           else xH      (* Entry point. *)
                     ) in
        (* * 1. Allocate stack frame.
           * 2. Call callee
           * 3. Insert return label (callee will jump back here).
           * 4. Free stack frame.
           * 5. Continue.
           *)
        (lbl, Before
              ++ MkLI ii (Lcall (ovari_of_ra ra) lcall)
              :: MkLI ii (ReturnTarget lret)
              :: After
              ++ lc
          )
    else (lbl, lc )

  | Cfor _ _ _ => (lbl, lc)
  end.

(* returns the end point of the linear translation of i, given n0 as
   its start point *)
Fixpoint linear_end_i (fn: funname) (i:instr) (n0: nat) : nat :=
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ _ => n0 (* absurd case *)

  | Copn xs _ o es =>
      match oseq.omap lexpr_of_lval xs, oseq.omap rexpr_of_pexpr es with
      | Some xs, Some es => S n0
      | _, _ => n0 (* absurd case *)
      end

  | Csyscall xs o es => S n0
                          
  | Cif e [::] c2 =>
      let n1 := linear_end_c linear_end_i fn c2 (S n0) in S n1

  | Cif e c1 [::] =>
      let n1 := linear_end_c linear_end_i fn c1 (S n0) in S n1
        
  | Cif e c1 c2 =>
      let n1 := linear_end_c linear_end_i fn c2 (S n0) in
      let n2 := linear_end_c linear_end_i fn c1 (S (S n1)) in S n2
        
  | Cwhile a c e _ c' =>
   let aI := match a with
             | NoAlign => 0
             | Align => 1
             end in             
    match is_bool e with
    | Some true =>
      let n1 := linear_end_c linear_end_i fn c (S n0 + aI) in
      let n2 := linear_end_c linear_end_i fn c' n1 in S n2

    | Some false => linear_end_c linear_end_i fn c n0
                              
    | None =>
      match c' with
      | [::] =>
          let n3 := linear_end_c linear_end_i fn c (S n0 + aI) in S n3
                                                         
      | _ =>
         let n1 := linear_end_c linear_end_i fn c' (S n0 + aI + 1) in
         let n2 := linear_end_c linear_end_i fn c (S n1) in S n2
      end
    end     
           
  | Ccall xs fn' es =>
    if get_fundef (p_funcs p) fn' is Some fd then
      let e := f_extra fd in
      let ra := sf_return_address e in
      if is_RAnone ra then n0
      else
        let sz := stack_frame_allocation_size e in
        let tmp := tmpi_of_ra ra in
        let before := allocate_stack_frame false ii sz tmp
                        (is_RAstack_None_call ra) in
        let bn := List.length before in 
        n0 + 2 * (bn + 1)
    else n0 
           
  | Cfor _ _ _ => n0
  end.


(* alternative definition of linear_i, inclusive of start and end
   points (currently not needed). *)
Fixpoint linear_full_i (fn: funname) (i:instr) (n0: nat) (lbl0:label) :
  (nat * label * lcmd) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ _ => (n0, lbl0, nil) (* absurd case *)
  | Copn xs _ o es =>
      match oseq.omap lexpr_of_lval xs, oseq.omap rexpr_of_pexpr es with
      | Some xs, Some es => (S n0, lbl0, [:: MkLI ii (Lopn xs o es)])
      | _, _ => (n0, lbl0, nil) (* absurd case *)
      end

  | Csyscall xs o es => (S n0, lbl0, [:: MkLI ii (Lsyscall o)])
                          
  | Cif e [::] c2 =>
      let lbl1 := next_lbl lbl0 in
      let '(n2, lbl2, lc) :=
        linear_full_c linear_full_i fn c2 (S n0) lbl1 in     
      (S n2, lbl2,
        (MkLI ii (Lcond (to_fexpr e) lbl0)) ::
          (lc ++ [:: (MkLI ii (Llabel lbl1))]))

  | Cif e c1 [::] =>
      let lbl1 := next_lbl lbl0 in
      let '(n2, lbl2, lc) :=
        linear_full_c linear_full_i fn c1 (S n0) lbl1 in     
      (S n2, lbl2,
        (MkLI ii (Lcond (to_fexpr (snot e)) lbl0)) ::
          (lc ++ [:: (MkLI ii (Llabel lbl1))]))
        
  | Cif e c1 c2 =>
      let lbl1 := next_lbl lbl0 in
      let lbl2 := next_lbl lbl1 in
      (* this is different from the original def, because there the 
          labels for c2 comes AFTER the labels of c1. *)
      let '(n3, lbl3, lc2) :=
        linear_full_c linear_full_i fn c2 (S n0) lbl2 in
      let '(n4, lbl4, lc1) :=
        linear_full_c linear_full_i fn c1 (S (S n3)) lbl3 in
      (S n4, lbl4,
        MkLI ii (Lcond (to_fexpr e) lbl0) ::
          (lc2 ++ (MkLI ii (Lgoto (fn, lbl1)) ::
                     (MkLI ii (Llabel lbl0) ::
                       (lc1 ++ [:: (MkLI ii (Llabel lbl1))])))))    
        
  | Cwhile a c e _ c' =>
    match is_bool e with
    | Some true =>
      let lbl1 := next_lbl lbl0 in
      let '(n2, lbl2, lc2) :=
        linear_full_c linear_full_i fn c (S n0) lbl1 in
      let '(n3, lbl3, lc1) :=
        linear_full_c linear_full_i fn c' n2 lbl2 in
      (S n3, lbl3,  
       (add_align ii a ((MkLI ii (Llabel lbl0)) :: (lc2 ++ lc1 ++
                             [:: (MkLI ii (Lgoto (fn, lbl0)))]))))

    | Some false =>
      linear_full_c linear_full_i fn c n0 lbl0 

    | None =>
      match c' with
      | [::] =>
         let lbl1 := next_lbl lbl0 in
         let '(n2, lbl2, lc2) :=
           linear_full_c linear_full_i fn c (S n0) lbl1 in
         (S n2, lbl2, add_align ii a (MkLI ii (Llabel lbl0) ::
                          (lc2 ++ 
                             [:: (MkLI ii (Lcond (to_fexpr e) lbl0))])))
      | _ =>
         let lbl1 := next_lbl lbl0 in
         let lbl2 := next_lbl lbl1 in
         let '(n3, lbl3, lc2) :=
           linear_full_c linear_full_i fn c' (S n0) lbl2 in
         let '(n4, lbl4, lc1) :=
           linear_full_c linear_full_i fn c (S n3) lbl3 in   
         (S n4, lbl4, (MkLI ii (Lgoto (fn, lbl0)) ::         
           (add_align ii a (MkLI ii (Llabel lbl1) ::
                          (lc2 ++ (MkLI ii (Llabel lbl0) :: (lc1 ++
                    [:: (MkLI ii (Lcond (to_fexpr e) lbl0))])))))))
      end
    end     
           
  | Ccall xs fn' es =>
    if get_fundef (p_funcs p) fn' is Some fd
    then
      let e := f_extra fd in
      let ra := sf_return_address e in
      if is_RAnone ra
      then (n0, lbl0, nil)
      else
        let sz := stack_frame_allocation_size e in
        let tmp := tmpi_of_ra ra in
        let Before :=
          allocate_stack_frame false ii sz tmp (is_RAstack_None_call ra) in
        let After :=
          allocate_stack_frame true ii sz tmp (is_RAstack_None_return ra) in
      (*  let lret := lbl0 in *)
        let lbl1 := next_lbl lbl0 in
        (* The test is used for the proof of linear_has_valid_labels *)
      (*  let lcall := (fn', if fn' == fn
                           then lbl0    (* Absurd case. *)
                           else xH      (* Entry point. *)
                     ) in *)
        let lcall := (fn', xH) in
        (* * 1. Allocate stack frame.
           * 2. Call callee
           * 3. Insert return label (callee will jump back here).
           * 4. Free stack frame.
           * 5. Continue.
           *)
        let n1 := List.length Before in
        (n0 + 2 * (n1 + 1), lbl1, Before
              ++ MkLI ii (Lcall (ovari_of_ra ra) lcall)
              :: MkLI ii (ReturnTarget lbl0)
              :: After
          )
    else (n0, lbl0, nil)
           
  | Cfor _ _ _ => (n0, lbl0, nil)
  end.


Definition linear_body (fi: fun_info) (e: stk_fun_extra) (body: cmd) :
  label * lcmd :=
  let fentry_ii := entry_info_of_fun_info fi in
  let ret_ii := ret_info_of_fun_info fi in
  let: (tail, head, lbl) :=
     match sf_return_address e with
     | RAreg r _ =>
       ( [:: MkLI ret_ii (Ligoto (Rexpr (Fvar (mk_var_i r)))) ]
       , [:: MkLI fentry_ii (Llabel 1) ]
       , 2%positive
       )
     | RAstack ra_call ra_return z _ =>
       ( if ra_return is Some ra_return
         then [:: lload ret_ii (mk_var_i ra_return) rspi z;
                  MkLI ret_ii (Ligoto (Rexpr (Fvar (mk_var_i ra_return)))) ]
         else [:: MkLI ret_ii Lret ]
       , MkLI fentry_ii (Llabel 1) ::
         (if ra_call is Some ra_call
          then [:: lstore fentry_ii rspi z (mk_var_i ra_call) ]
          else [::])
       , 2%positive
       )
     | RAnone =>
       let sf_sz := (sf_stk_sz e + sf_stk_extra_sz e)%Z in
       match sf_save_stack e with
       | SavedStackNone =>
         ([::], [::], 1%positive)
       | SavedStackReg x =>
         (* Tail: R[rsp] := R[x]
          * Head: R[x] := R[rsp]
          *       Setup stack.
          *)
         let r := mk_var_i x in
         ( [:: lmove ret_ii rspi r ]
         , set_up_sp_register fentry_ii rspi sf_sz (sf_align e) r (mk_var_i var_tmp)
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
         let r := mk_var_i var_tmp in
         ( pop_to_save ret_ii e.(sf_to_save) ofs
         , set_up_sp_register fentry_ii rspi sf_sz (sf_align e) r (mk_var_i var_tmp2)
             ++ push_to_save fentry_ii e.(sf_to_save) (var_tmp, ofs)
         , 1%positive)
       end
     end
  in
  let fd' := linear_c linear_i body lbl tail in
  (fd'.1, head ++ fd'.2).


Definition linear_fd (fd: sfundef) :=
  let e := fd.(f_extra) in
  let is_export := is_RAnone (sf_return_address e) in
  let res := if is_export then f_res fd else [::] in
  let body := linear_body fd.(f_info) e fd.(f_body) in
  (body.1,
    {| lfd_info := f_info fd
    ; lfd_align := sf_align e
    ; lfd_tyin := f_tyin fd
    ; lfd_arg := f_params fd
    ; lfd_body := body.2
    ; lfd_tyout := f_tyout fd
    ; lfd_res := res
    ; lfd_export := is_export
    ; lfd_callee_saved := if is_export then map fst e.(sf_to_save) else [::]
    ; lfd_stk_max := sf_stk_max e
    ; lfd_frame_size := frame_size e
    ; lfd_align_args := sf_align_args e
    |}).


Notation plinfo := (nat * label)%type.

Variant LAtomL (fn: funname) (lbl: label) : Type :=
| MkLAtomL (ii: instr_info) (l: label_kind). 

Definition incrP1 (pl: plinfo) := (S (fst pl), snd pl).

Definition does_align (ii: instr_info) (a: expr.align) : bool :=
  match a with | NoAlign => false | Align => true end.

Inductive LTree (fn0: funname) : plinfo -> plinfo -> Type :=
| LErrLeaf : forall pl, LTree pl pl
| LLeaf : forall pl,
   linstr -> LTree pl (incrP1 pl)
| LLeafL : forall pl,
   let n0 := fst pl in
   let lbl0 := snd pl in
   let lbl1 := next_lbl lbl0 in
   LAtomL fn0 lbl0 -> LTree pl (S n0, lbl1)
| LIf1Node : forall pl0 pl1,
   let n0 := fst pl0 in
   let lbl0 := snd pl0 in
   let lbl01 := next_lbl lbl0 in
   forall (la_cond: linstr)
          (lcm1: LTreeList (S n0, lbl01) pl1)
          (la_label1: LAtomL fn0 lbl0),
   LTree pl0 (incrP1 pl1)           
| LIfNode : forall pl0 pl1 pl2,
   let n0 := fst pl0 in
   let lbl0 := snd pl0 in
   let lbl01 := next_lbl lbl0 in
   let lbl02 := next_lbl lbl01 in
   let n1 := fst pl1 in
   let lbl1 := snd pl1 in
   forall (la_cond1: linstr)
          (lcm2: LTreeList (S n0, lbl02) pl1)
          (la_goto2: linstr)
          (la_label1: LAtomL fn0 lbl0)
          (lcm1: LTreeList (S (S n1), lbl1) pl2)
          (la_label2: LAtomL fn0 lbl01),
   LTree pl0 (incrP1 pl2)                  
| LWhileTNode : forall pl0 pl1 pl2 (la_align: bool), 
   let n0 := fst pl0 in
   let lbl0 := snd pl0 in
   let n00 := if la_align then S n0 else n0 in  
   let lbl01 := next_lbl lbl0 in
   forall (la_label1: LAtomL fn0 lbl0)
          (lcm1: LTreeList (S n00, lbl01) pl1)
          (lcm2: LTreeList pl1 pl2)
          (la_goto1: linstr),
   LTree pl0 (incrP1 pl2)            
| LWhileFNode : forall pl0 pl1 (lcm1: LTreeList pl0 pl1),
   LTree pl0 pl1    
| LWhile1Node : forall pl0 pl1 (la_align: bool),
   let n0 := fst pl0 in
   let lbl0 := snd pl0 in
   let n00 := if la_align then S n0 else n0 in  
   let lbl01 := next_lbl lbl0 in
   let n1 := fst pl1 in
   let lbl1 := snd pl1 in
   forall (la_label1: LAtomL fn0 lbl0)
          (lcm1: LTreeList (S n00, lbl01) pl1)
          (la_cond1: linstr),
   LTree pl0 (incrP1 pl1)  
| LWhileNode : forall pl0 pl1 pl2 (la_align: bool),
   let n0 := fst pl0 in
   let lbl0 := snd pl0 in
   let n00 := if la_align then S n0 else n0 in  
   let lbl01 := next_lbl lbl0 in
   let lbl02 := next_lbl lbl01 in
   let n1 := fst pl1 in
   let lbl1 := snd pl1 in
   forall (la_goto1: linstr)
          (la_label2: LAtomL fn0 lbl01)
          (lcm2: LTreeList (S (S n00), lbl02) pl1)
          (la_label1: LAtomL fn0 lbl0)
          (lcm1: LTreeList (S n1, lbl1) pl2)
          (la_cond2: linstr),
   LTree pl0 (incrP1 pl2)  
| LCallNode : forall pl0 nb na,
   let n0 := fst pl0 in
   let lbl0 := snd pl0 in
   let lbl1 := next_lbl lbl0 in
   let n1 := n0 + nb in
   let n2 := S n1 in 
   forall (fn': funname)
          (la_before la_after: lcmd),
     forall (la_call: linstr)
            (la_ret: LAtomL fn0 lbl0),
     LTree pl0 (n2 + na, lbl1)        
with LTreeList (fn0: funname) : plinfo -> plinfo -> Type := 
| LListNil : forall pl, LTreeList pl pl
| LListCons : forall pl0 pl1 pl2,
    LTree pl0 pl1 -> LTreeList pl1 pl2 -> LTreeList pl0 pl2.

Fixpoint interm_cmd
  (LI: forall (fn0: funname) (i: instr) (pl0: plinfo),
      sigT (fun pl1 => LTree fn0 pl0 pl1))
  (fn0: funname) (cc: cmd) (pl0: plinfo) :
  sigT (fun pl1 => LTreeList fn0 pl0 pl1) :=
       match cc with
       | nil =>   
          existT _ pl0 (LListNil fn0 pl0)
       | i :: cc0 =>
           let: (n0, lbl0) := pl0 in
           let X1 := LI fn0 i pl0 in
           let pl1 := projT1 X1 in
           let X2 := interm_cmd LI fn0 cc0 pl1 in
           let: pl2 := projT1 X2 in 
           existT _ pl2 (@LListCons fn0 pl0 pl1 pl2  
                                    (projT2 X1) (projT2 X2)) end.

Fixpoint interm_i
  (LC: forall (fn0: funname) (c: cmd) (pl0: plinfo),
      sigT (fun pl1 => LTreeList fn0 pl0 pl1))
  (fn0: funname) (i: instr) (pl0: plinfo) :
  sigT (fun pl1 => LTree fn0 pl0 pl1) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ _ =>
      existT _ pl0 (LErrLeaf fn0 pl0)  (* absurd case *)
             
  | Copn xs _ o es =>
      match oseq.omap lexpr_of_lval xs, oseq.omap rexpr_of_pexpr es with
      | Some xs, Some es =>
          let atm := MkLI ii (Lopn xs o es) in 
          existT _ (incrP1 pl0) (LLeaf fn0 pl0 atm)
      | _, _ =>
          existT _ pl0 (LErrLeaf fn0 pl0) (* absurd case *)
      end
        
  | Csyscall xs o es =>
    let atm := MkLI ii (Lsyscall o) in 
    existT _ (incrP1 pl0) (LLeaf fn0 pl0 atm)

  | Cif e [::] c2 =>
    let n0 := fst pl0 in
    let lbl0 := snd pl0 in
    let lbl01 := next_lbl lbl0 in
    let A1 := MkLI ii (Lcond (to_fexpr e) lbl0) in
    let X1 := LC fn0 c2 (S n0, lbl01) in
    let pl1 := projT1 X1 in
    let A2 := MkLAtomL fn0 lbl0 ii InternalLabel in 
    existT _ (incrP1 pl1) (@LIf1Node fn0 pl0 pl1 A1 (projT2 X1) A2)
           
  | Cif e c1 [::] =>
    let n0 := fst pl0 in
    let lbl0 := snd pl0 in
    let lbl01 := next_lbl lbl0 in
    let A1 := MkLI ii (Lcond (to_fexpr e) lbl0) in
    let X1 := LC fn0 c1 (S n0, lbl01) in
    let pl1 := projT1 X1 in
    let A2 := MkLAtomL fn0 lbl0 ii InternalLabel in 
    existT _ (incrP1 pl1) (@LIf1Node fn0 pl0 pl1 A1 (projT2 X1) A2)

  | Cif e c1 c2 =>
    let n0 := fst pl0 in
    let lbl0 := snd pl0 in
    let lbl01 := next_lbl lbl0 in
    let lbl02 := next_lbl lbl01 in
    let A1 := MkLI ii (Lcond (to_fexpr e) lbl0) in
    let X2 := LC fn0 c2 (S n0, lbl02) in
    let pl1 := projT1 X2 in
    let n1 := fst pl1 in
    let lbl1 := snd pl1 in
    let A2 := MkLI ii (Lgoto (fn0, lbl1)) in
    let A3 := MkLAtomL fn0 lbl0 ii InternalLabel in 
    let X1 := LC fn0 c1 (S (S n1), lbl1) in
    let pl2 := projT1 X1 in
    let A4 := MkLAtomL fn0 lbl01 ii InternalLabel in 
    existT _ (incrP1 pl2) (@LIfNode fn0 pl0 pl1 pl2 A1
                             (projT2 X2) A2 A3 (projT2 X1) A4)

  | Cwhile a c1 e _ c2 =>
  let n0 := fst pl0 in
(*  let lbl0 := snd pl0 in
    let la_align := does_align ii a in
    let n00 := if la_align then n0 else S n0 in  *)
    match is_bool e with
    | Some true =>
      let n0 := fst pl0 in
      let lbl0 := snd pl0 in
      let la_align := does_align ii a in
      let n00 := if la_align then S n0 else n0 in 
      
      let lbl01 := next_lbl lbl0 in
      let A1 := MkLAtomL fn0 lbl0 ii InternalLabel in 
      let X1 := LC fn0 c1 (S n00, lbl01) in
      let pl1 := projT1 X1 in
      let X2 := LC fn0 c2 pl1 in
      let pl2 := projT1 X2 in
      let A2 := MkLI ii (Lgoto (fn0, lbl0)) in
      existT _ (incrP1 pl2) (@LWhileTNode fn0 pl0 pl1 pl2 la_align
                               A1 (projT2 X1) (projT2 X2) A2)
    | Some false =>        
      let X1 := LC fn0 c1 pl0 in
      let pl1 := projT1 X1 in   
      existT _ pl1 (@LWhileFNode fn0 pl0 pl1 (projT2 X1))
             
    | None =>
      match c2 with
      | [::] =>  
        let n0 := fst pl0 in
        let lbl0 := snd pl0 in
        let la_align := does_align ii a in
        let n00 := if la_align then S n0 else n0 in 

        let lbl01 := next_lbl lbl0 in
        let A1 := MkLAtomL fn0 lbl0 ii InternalLabel in 
        let X1 := LC fn0 c1 (S n00, lbl01) in
        let pl1 := projT1 X1 in       
        let A2 := MkLI ii (Lcond (to_fexpr e) lbl0) in
        existT _ (incrP1 pl1) (@LWhile1Node fn0 pl0 pl1 la_align
                                 A1 (projT2 X1) A2)

      | _ =>
        let n0 := fst pl0 in
        let lbl0 := snd pl0 in
        let la_align := does_align ii a in
        let n00 := if la_align then S n0 else n0 in 
          
        let lbl01 := next_lbl lbl0 in
        let lbl02 := next_lbl lbl01 in
        let A1 := MkLI ii (Lgoto (fn0, lbl0)) in
        let A2 := MkLAtomL fn0 lbl01 ii InternalLabel in 
        let X2 := LC fn0 c2 (S (S n00), lbl02) in
        let pl1 := projT1 X2 in
        let A3 := MkLAtomL fn0 lbl0 ii InternalLabel in 
        let X1 := LC fn0 c1 (incrP1 pl1) in
        let pl2 := projT1 X1 in
        let A4 := MkLI ii (Lcond (to_fexpr e) lbl0) in
        existT _ (incrP1 pl2) (@LWhileNode fn0 pl0 pl1 pl2 la_align
                               A1 A2 (projT2 X2) A3 (projT2 X1) A4)
     end                                                                    
    end

  | Ccall xs fn' es =>
    let n0 := fst pl0 in
    let lbl0 := snd pl0 in
    let lbl1 := next_lbl lbl0 in

    if get_fundef (p_funcs p) fn' is Some fd
    then
      let e := f_extra fd in
      let ra := sf_return_address e in
      if is_RAnone ra
      then existT _ pl0 (LErrLeaf fn0 pl0)  (* absurd case *)
      else
        let sz := stack_frame_allocation_size e in
        let tmp := tmpi_of_ra ra in
        let Before :=
          allocate_stack_frame false ii sz tmp (is_RAstack_None_call ra) in
        let After :=
          allocate_stack_frame true ii sz tmp (is_RAstack_None_return ra) in
        let lcall := (fn', xH) in
        let nb := List.length Before in
        let na := List.length After in
        let n1 := n0 + nb in
        let n2 := S n1 + na in 
        let A1 := MkLI ii (Lcall (ovari_of_ra ra) lcall) in
        let A2 := MkLAtomL fn0 lbl0 ii ExternalLabel in 
        existT _ (n2, lbl1) (@LCallNode fn0 pl0 nb na fn' Before After A1 A2)   
        
    else existT _ pl0 (LErrLeaf fn0 pl0)  (* absurd case *)

  | _ => existT _ pl0 (LErrLeaf fn0 pl0)   (* absurd case, no for loops *)
  end.


(*
Fixpoint interm_i (fn0: funname) (i: instr) (pl0: plinfo) :
  sigT (fun pl1 => LTree fn0 pl0 pl1) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ _ =>
      existT _ pl0 (LErrLeaf fn0 pl0)  (* absurd case *)

  | Copn xs _ o es =>
      match oseq.omap lexpr_of_lval xs, oseq.omap rexpr_of_pexpr es with
      | Some xs, Some es =>
          let atm := MkLAtom fn0 (fst pl0) ii (Lopn xs o es) in 
          existT _ (incrP1 pl0) (LLeaf atm)
      | _, _ =>
          existT _ pl0 (LErrLeaf fn0 pl0) (* absurd case *)
      end
        
  | Csyscall xs o es =>
    let atm := MkLAtom fn0 (fst pl0) ii (Lsyscall o) in 
    existT _ (incrP1 pl0) (LLeaf atm)
           
  | _ => existT _ pl0 (LErrLeaf fn0 pl0)
  end
with interm_cmd (fn0: funname) (cc: cmd) (pl0: plinfo) :
  sigT (fun pl1 => LTreeList fn0 pl0 pl1) :=
       match cc with
       | nil =>   
          existT _ pl0 (LListNil fn0 pl0)
       | i :: cc0 =>
           let: (n0, lbl0) := pl0 in
           let X1 := interm_i fn0 i pl0 in
           let pl1 := projT1 X1 in
           let X2 := interm_cmd fn0 cc0 pl1 in
           let: pl2 := projT1 X2 in 
           existT _ pl2 (@LListCons fn0 pl0 pl1 pl2  
                                    (projT2 X1) (projT2 X2)) end.
*)

(*
Fixpoint interm_i (fn0: funname) (i:instr) (pl0: plinfo) :
  sigT (fun pl1 => LTree fn0 pl0 pl1) :=
  let '(n0, lbl) := pl0 in 
  let (ii, ir) := i in
  existT _ pl0 (LErrLeaf fn0 pl0).

Proof.
  destruct i as [ii ir].
  econstructor.
  instantiate (1:= pl0).
  exact (LErrLeaf fn0 pl0).
  Show Proof.
*)

(*
Definition if_align_else (ii: instr_info) (a: expr.align) (n0 n1: nat) :
  nat := match a with | NoAlign => n0 | Align => n1 end.
*)
(*
Variant LAtom (fn0: funname) (n: nat) : Type :=
| MkLAtom (ii: instr_info) (i: linstr_r).  
*)


End FUN.

Definition linear_prog : cexec lprog :=
  Let _ := check_prog in
  Let _ := assert (size p.(p_globs) == 0)
             (E.internal_error "invalid p_globs") in
  let funcs := fmap (fun nb_lbl '(f,fd) =>
    let fd := linear_fd f fd in
    ((nb_lbl + fd.1)%positive, (f, fd.2))) 1%positive p.(p_funcs)
  in
  Let _ := assert (funcs.1 <=? wbase Uptr)%Z
                  (E.internal_error "too many labels")
  in
  ok {| lp_rip   := p.(p_extra).(sp_rip);
        lp_rsp   := p.(p_extra).(sp_rsp);
        lp_globs := p.(p_extra).(sp_globs);
        lp_glob_names := p.(p_extra).(sp_glob_names);
        lp_funcs := funcs.2 |}.

End PROG.
End WITH_PARAMS.
