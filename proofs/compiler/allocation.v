(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.
Require Import strings expr.
Require Import compiler_util ZArith sem_pexpr_params.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Module E.

Definition pass_name := "allocation"%string.

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

Definition error msg := gen_error true None msg.

Definition loop_iterator := loop_iterator pass_name.

Definition fold2 := error "fold2".

End E.

Module Type CheckB.

  Module M.
    Parameter t : Type.
    Parameter empty : t.
    Parameter merge : t -> t -> t.
    Parameter incl  : t -> t -> bool.

  End M.

  Parameter check_e    : pexpr -> pexpr -> M.t -> cexec M.t.

  Parameter check_lval : option (stype * pexpr) -> lval -> lval -> M.t -> cexec M.t.

End CheckB.

Module Type CheckBE.
  Include CheckB.

  Section WITH_PARAMS.
  Context
    {asm_op syscall_state : Type}
    {spp : SemPexprParams asm_op syscall_state}.

  Parameter eft : SemPexprParams asm_op syscall_state -> eqType.
  #[ global ] Arguments eft {_}.

  #[ global ] Declare Instance pT  : progT eft.

  Parameter init_alloc :
    extra_fun_t -> extra_prog_t -> extra_prog_t -> cexec M.t.

  End WITH_PARAMS.
End CheckBE.

Module CheckBU (C:CheckB) <: CheckBE.

  Include C.

  Section WITH_PARAMS.
  Context
    {asm_op syscall_state : Type}
    {spp : SemPexprParams asm_op syscall_state}.

  Definition eft := fun {_: SemPexprParams asm_op syscall_state} => [eqType of unit].
  #[ global ] Instance pT : progT eft := progUnit.

  Definition init_alloc (ef: extra_fun_t) (ep1 ep2: extra_prog_t) : cexec M.t :=
    ok M.empty.

  End WITH_PARAMS.
End CheckBU.

Definition alloc_error := pp_internal_error_s "allocation".

Module CheckBS (C:CheckB) <: CheckBE.

  Include C.

  Section WITH_PARAMS.
  Context
    {asm_op syscall_state : Type}
    {spp : SemPexprParams asm_op syscall_state}.

  Definition eft := extra_fun_t (pT:= progStack).
  Instance pT : progT eft := progStack.
 
  Definition check_lvals :=
    fold2 E.fold2 (check_lval None).

  Definition check_vars xs1 xs2 r := check_lvals (map Lvar xs1) (map Lvar xs2) r.

  Definition init_alloc (ef: extra_fun_t) (ep1 ep2: extra_prog_t) : cexec M.t :=
    check_vars [:: vid ep1.(sp_rsp); vid ep1.(sp_rip)]
               [:: vid ep2.(sp_rsp); vid ep2.(sp_rip)] M.empty.

  End WITH_PARAMS.
End CheckBS.

Module MakeCheckAlloc (C:CheckBE).

Import C.

Section LOOP.

  Variable check_c : M.t -> cexec M.t.

  Fixpoint loop (n:nat) (m:M.t) :=
    match n with
    | O => Error E.loop_iterator 
    | S n =>
      Let m' := check_c m in
      if M.incl m m' then ok m
      else loop n (M.merge m m')
    end.

  Variable check_c2 : M.t -> cexec (M.t * M.t).

  Fixpoint loop2 (n:nat) (m:M.t) :=
    match n with
    | O => Error E.loop_iterator 
    | S n =>
      Let m' := check_c2 m in
      if M.incl m m'.2 then ok m'.1
      else loop2 n (M.merge m m'.2)
    end.

End LOOP.


Definition check_es es1 es2 r := fold2 E.fold2 check_e es1 es2 r.

Definition check_lvals := fold2 E.fold2 (check_lval None).

Definition check_var x1 x2 r := check_lval None (Lvar x1) (Lvar x2) r.

Definition check_vars xs1 xs2 r := check_lvals (map Lvar xs1) (map Lvar xs2) r.

Section WITH_PARAMS.
Context
  {asm_op syscall_state : Type}
  {spp : SemPexprParams asm_op syscall_state}.

Fixpoint check_i (i1 i2:instr_r) r :=
  match i1, i2 with
  | Cassgn x1 _ ty1 e1, Cassgn x2 _ ty2 e2 =>
    if ty1 == ty2 then
     check_e e1 e2 r >>= check_lval (Some (ty2,e2)) x1 x2
    else Error (alloc_error "bad type in assignment")
  | Copn xs1 _ o1 es1, Copn xs2 _ o2 es2 =>
    if o1 == o2 then
      check_es es1 es2 r >>= check_lvals xs1 xs2
    else Error (alloc_error "operators not equals")
  | Csyscall xs1 o1 es1, Csyscall xs2 o2 es2 =>
    if o1 == o2 then
      check_es es1 es2 r >>= check_lvals xs1 xs2
    else Error (alloc_error "operators not equals")

  | Ccall _ x1 f1 arg1, Ccall _ x2 f2 arg2 =>
    if f1 == f2 then
      check_es arg1 arg2 r >>= check_lvals x1 x2
    else Error (alloc_error "functions not equals")
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    Let re := check_e e1 e2 r in
    Let r1 := fold2 E.fold2 check_I c11 c21 re in
    Let r2 := fold2 E.fold2 check_I c12 c22 re in
    ok (M.merge r1 r2)
  | Cfor x1 (d1,lo1,hi1) c1, Cfor x2 (d2,lo2,hi2) c2 =>
    if d1 == d2 then
      Let rhi := check_e lo1 lo2 r >>=check_e hi1 hi2 in
      let check_c r :=
          check_var x1 x2 r >>=
          fold2 E.fold2 check_I c1 c2 in
      loop check_c Loop.nb rhi
    else Error (alloc_error "loop directions not equals")
  | Cwhile a1 c1 e1 c1', Cwhile a2 c2 e2 c2' =>
    let check_c r :=
      Let r := fold2 E.fold2 check_I c1 c2 r in
      Let re := check_e e1 e2 r in
      Let r' := fold2 E.fold2 check_I c1' c2' re in
      ok (re, r') in
    Let r := loop2 check_c Loop.nb r in
    ok r

  | _, _ => Error (alloc_error "instructions not equals")
  end

with check_I i1 i2 r :=
  match i1, i2 with
  | MkI _ i1, MkI ii i2 => check_i i1 i2 r
  end.

Definition check_cmd := fold2 E.fold2 check_I.

Definition check_fundef (ep1 ep2 : extra_prog_t) (f1 f2: funname * fundef) (_:Datatypes.unit) :=

  let (f1,fd1) := f1 in
  let (f2,fd2) := f2 in
  add_funname f1 (add_finfo fd1.(f_info) (
  if (f1 == f2) && (fd1.(f_tyin) == fd2.(f_tyin)) && (fd1.(f_tyout) == fd2.(f_tyout)) &&
      (fd1.(f_extra) == fd2.(f_extra)) then
    Let r := init_alloc fd1.(f_extra) ep1 ep2 in
    Let r := check_vars fd1.(f_params) fd2.(f_params) r in
    Let r := check_cmd fd1.(f_body) fd2.(f_body) r in
    let es1 := map Plvar fd1.(f_res) in
    let es2 := map Plvar fd2.(f_res) in
    Let _r := check_es es1 es2 r in
    ok tt
  else Error (E.error "functions not equals"))).

Definition check_prog_error := alloc_error "check_fundef (fold2)".

Definition check_prog ep1 p_funcs1 ep2 p_funcs2 := 
  fold2 check_prog_error (check_fundef ep1 ep2) p_funcs1 p_funcs2 tt.

End WITH_PARAMS.

End MakeCheckAlloc.

Module CBAreg.

  Module M.

  Module Mv.

  Definition oget (mid: Mvar.t Sv.t) id := odflt Sv.empty (Mvar.get mid id).

  Definition valid (mvar: Mvar.t var) (mid: Mvar.t Sv.t) :=
    forall x id, Mvar.get mvar x = Some id <-> Sv.In x (oget mid id).

  Record t_ := mkT { mvar : Mvar.t var; mid : Mvar.t Sv.t }.
  Definition t := t_.

  Definition get (m:t) (x:var) := Mvar.get (mvar m) x.

  Definition rm_id (m:t) id :=
     Sv.fold (fun x m => Mvar.remove m x) (oget (mid m) id) (mvar m).

  Definition ms_upd (m:Mvar.t Sv.t) (f:Sv.t -> Sv.t) id :=
    Mvar.set m id (f (oget m id)).

  Definition rm_x (m:t) x :=
    match Mvar.get (mvar m) x with
    | Some id => ms_upd (mid m) (Sv.remove x) id
    | None    => (mid m)
    end.

  Definition remove m id := @mkT (rm_id m id) (Mvar.remove (mid m) id).

  Definition set m x id := mkT (Mvar.set (rm_id m id) x id) (Mvar.set (rm_x m x) id (Sv.singleton x)).

  Definition add m x id := mkT (Mvar.set (mvar m) x id) (ms_upd (rm_x m x) (fun s => Sv.add x s) id).

  Definition empty := mkT (@Mvar.empty _) (@Mvar.empty _).

  End Mv.


  Record t_ := mkT {
    mv : Mv.t;
    mset : Sv.t;
  }.

  Definition t := t_.

  Definition get (m:t) (x:var) := Mv.get (mv m) x.

  Definition set m x id := mkT (Mv.set (mv m) x id) (Sv.add x (mset m)).
  Arguments set m x id : clear implicits.

  Definition add m x id := mkT (Mv.add (mv m) x id) (Sv.add x (mset m)).
  Arguments add m x id : clear implicits.

  Definition addc m x id := add m x id. (*
    if v_wextendtyP x id is left h then add m x id h
    else m. *)

  Definition empty_s s := mkT Mv.empty s.

  Definition empty := empty_s Sv.empty.

  Definition merge_aux m1 m2 :=
    Mvar.map2 (fun x ox ox' =>
      match ox, ox' with
      | Some idx, Some idx' => if idx == idx' then Some idx else None
      | Some idx, None      => if ~~(Sv.mem x (mset m2)) then Some idx else None
      | None, Some idx      => if ~~(Sv.mem x (mset m1)) then Some idx else None
      | None, None          => None
      end) (Mv.mvar m1.(mv)) (Mv.mvar m2.(mv)).

  Definition merge m1 m2 :=
    let mv := merge_aux m1 m2 in
    Mvar.fold (fun x idx m => addc m x idx) mv (empty_s (Sv.union (mset m1) (mset m2))).

  Definition remove m id :=  mkT (Mv.remove (mv m) id) (mset m).

  Definition incl m1 m2 :=
    Sv.subset (mset m2) (mset m1) &&
    let mv1 := Mv.mvar m1.(mv) in
    let mv2 := Mv.mvar m2.(mv) in
    Sv.for_all (fun x =>
       match Mvar.get mv1 x with
       | Some idx => Mvar.get mv2 x == Some idx
       | None     => true
       end) (mset m2).

  End M.

  Definition cerr_varalloc xi1 xi2 s:=
    pp_internal_error "Variable allocation" (pp_box [:: pp_var xi1; pp_s "and"; pp_var xi2; pp_s ":"; pp_s s]).

  Definition check_v xi1 xi2 (m:M.t) : cexec M.t :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if true is true then
      match M.get m x1 with
      | None     =>
        if Sv.mem x1 (M.mset m) then 
            Error (cerr_varalloc xi1 xi2 "variable already set")
        else ok (M.set m x1 x2)
      | Some x2' =>
        if x2 == x2' then ok m
        else Error (cerr_varalloc xi1 xi2 "variable mismatch")
      end
    else Error (cerr_varalloc xi1 xi2 "type mismatch").

  Definition error_e := pp_internal_error_s "allocation" "expression are not equal".

  Definition check_gv x1 x2 (m:M.t) : cexec M.t :=
    if x1.(gs) == x2.(gs) then
      if is_lvar x1 then check_v x1.(gv) x2.(gv) m 
      else 
        if x1.(gv).(v_var) == x2.(gv).(v_var) then ok m
        else Error error_e
    else Error error_e.
 
  Fixpoint check_e (e1 e2:pexpr) (m:M.t) : cexec M.t :=
    match e1, e2 with
    | Pconst n1, Pconst n2 =>
      if n1 == n2 then ok m else Error error_e
    | Pbool  b1, Pbool  b2 =>
      if b1 == b2 then ok m else Error error_e
    | Parr_init n1, Parr_init n2 =>
      if n1 == n2 then ok m else Error error_e
    | Pvar   x1, Pvar   x2 => check_gv x1 x2 m
    | Pget aa1 w1 x1 e1, Pget aa2 w2 x2 e2 =>
      if (aa1 == aa2) && (w1 == w2) then check_gv x1 x2 m >>= check_e e1 e2 else Error error_e
    | Psub aa1 w1 len1 x1 e1, Psub aa2 w2 len2 x2 e2 =>
      if (aa1 == aa2) && (w1 == w2) && (len1 == len2) then check_gv x1 x2 m >>= check_e e1 e2 
      else Error error_e
    | Pload w1 x1 e1, Pload w2 x2 e2 =>
      if w1 == w2 then check_v x1 x2 m >>= check_e e1 e2 else Error error_e
    | Papp1 o1 e1, Papp1 o2 e2 =>
      if o1 == o2 then check_e e1 e2 m
      else Error error_e
     | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
      if o1 == o2 then check_e e11 e21 m >>= check_e e12 e22
      else Error error_e
    | PappN o1 es1, PappN o2 es2 =>
      if o1 == o2
      then fold2 (alloc_error "check_e (appN)") check_e es1 es2 m
      else Error error_e
    | Pif t e e1 e2, Pif t' e' e1' e2' =>
      if t == t' then
        check_e e e' m >>= check_e e1 e1' >>= check_e e2 e2'
      else Error error_e
    | _, _ => Error error_e
    end.

  Definition check_var (x1 x2:var) m : cexec M.t :=
    ok (M.set m x1 x2).

  Definition check_varc (xi1 xi2:var_i) m : cexec M.t :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if true is true then check_var x1 x2 m
    else Error (cerr_varalloc xi1 xi2 "type mismatch").

  Definition is_Pvar (e:option (stype * pexpr)) :=
    match e with
    | Some (ty, Pvar x) => if is_lvar x then Some (ty,x.(gv)) else None
    | _ => None
    end.

  Definition error_lv := pp_internal_error_s "allocation" "lval not equal".

  Definition check_lval (e2:option (stype * pexpr)) (x1 x2:lval) m : cexec M.t :=
    match x1, x2 with
    | Lnone  _ t1, Lnone _ t2  =>
      if true then ok m else Error error_lv
    | Lnone  _ t1, Lvar x      =>
      if true then
        ok (M.remove m x.(v_var))
      else Error error_lv
    | Lvar x1    , Lvar x2     =>
      match is_Pvar e2 with
      | Some (ty, x2') =>
        if true then
          if (vtype x1 == ty) && (vtype x1 == vtype x2) && (x2.(v_var) == x2') then ok (M.add m x1 x2)
          else check_var x1 x2 m
        else Error (cerr_varalloc x1 x2 "type mismatch")
      | _               => check_varc x1 x2 m
      end
    | Lmem w1 x1 e1, Lmem w2 x2 e2  =>
      if w1 == w2 then check_v x1 x2 m >>= check_e e1 e2 else Error error_lv
    | Laset aa1 w1 x1 e1, Laset aa2 w2 x2 e2 =>
      if (aa1 == aa2) && (w1 == w2) then check_v x1 x2 m >>= check_e e1 e2 >>= check_varc x1 x2
      else Error error_lv
    | Lasub aa1 w1 len1 x1 e1, Lasub aa2 w2 len2 x2 e2 =>
      if (aa1 == aa2) && (w1 == w2) && (len1 == len2) then check_v x1 x2 m >>= check_e e1 e2 >>= check_varc x1 x2
      else Error error_lv
 
    | _          , _           => Error error_lv
    end.

End CBAreg.

Module CBAregU := CheckBU CBAreg.
Module CheckAllocRegU :=  MakeCheckAlloc CBAregU.

Module CBAregS := CheckBS CBAreg.
Module CheckAllocRegS := MakeCheckAlloc CBAregS.
