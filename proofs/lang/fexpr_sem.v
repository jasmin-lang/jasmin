From mathcomp Require Import ssreflect ssrfun ssrbool ssralg.
Require Import fexpr.
Require Import psem.

Section SEM_EXPR.
(* Semantic of expressions *)

  Context {wsw : WithSubWord} {pd: PointerData}.
  Context (m: mem) (vm: Vm.t).

  Fixpoint sem_fexpr (e: fexpr) : exec value :=
    match e with
    | Fconst z => ok (Vint z)
    | Fvar x => get_var true vm x
    | Fapp1 op a => Let v := sem_fexpr a in sem_sop1 op v
    | Fapp2 op a b=> Let v := sem_fexpr a in Let w := sem_fexpr b in sem_sop2 op v w
    | Fif a b c => Let u := sem_fexpr a >>= to_bool in Let v := sem_fexpr b >>= to_bool in Let w := sem_fexpr c >>= to_bool in ok (Vbool (if u then v else w))
    end.

  Definition sem_rexpr (e: rexpr) : exec value :=
    match e with
    | Load al ws x a => Let p := get_var true vm x >>= to_pointer in Let off := sem_fexpr a >>= to_pointer in Let v := read m al (p + off)%R ws in ok (@to_val (sword ws) v)
    | Rexpr a => sem_fexpr a
    end.

End SEM_EXPR.

Section SEM.

Context
  {wsw : WithSubWord} {syscall_state : Type}
  {ep : EstateParams syscall_state}.

Definition write_lexpr e v (s: estate) : exec estate :=
  match e with
  | Store al ws x a =>
      Let p := get_var true (evm s) x >>= to_pointer in
      Let off := sem_fexpr (evm s) a >>= to_pointer in
      Let w := to_word ws v in
      Let m := write (emem s) al (p + off)%R w in
      ok (with_mem s m)
  | LLvar x =>
      Let vm := set_var true (evm s) x v in
      ok (with_vm s vm)
  end.

Definition sem_rexprs (s: estate) := mapM (sem_rexpr s.(emem) s.(evm)).
Definition write_lexprs := fold2 ErrType write_lexpr.

End SEM.
