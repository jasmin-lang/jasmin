(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import ZArith expr compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

(* ** unrolling
 * -------------------------------------------------------------------- *)

(** This pass is to be repeated until a fixed-point is reached.
  It returns a boolean indicating whether something happened,
  i.e., if the transformation should be repeated.
  Beware of wild monads…
*)
Section MAP_REPEAT.

Context {U V: Type} (f: U -> V * bool).

Definition map_repeat (m: seq U) : seq V * bool :=
  List.fold_right
    (fun u '(vs, a) =>
       let: (v, b) := f u in
       (v :: vs, a || b))
    ([::], false) m.

Lemma map_repeat_1 m :
  (map_repeat m).1 = [seq (f u).1 | u <- m].
Proof.
  elim: m; first by [].
  move => u m /=.
  case: map_repeat => _ b /= ->.
  by case: f.
Qed.

End MAP_REPEAT.

Section ASM_OP.

Context `{asmop:asmOp}.

Definition unroll_cmd (unroll_i: instr -> cmd * bool) (c:cmd) : cmd * bool :=
  List.fold_right
    (fun i '(c', a) =>
       let: (i', b) := unroll_i i in
       (i' ++ c', a || b))
    ([::], false) c.

Definition assgn ii x e := MkI ii (Cassgn (Lvar x) AT_inline x.(v_var).(vtype) e).

Fixpoint unroll_i (i: instr) : cmd * bool :=
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ _
  | Copn _ _ _ _
  | Csyscall _ _ _
  | Ccall _ _ _
    => ([:: i ], false)
  | Cif b c1 c2  =>
      let: (c1', b1) := unroll_cmd unroll_i c1 in
      let: (c2', b2) := unroll_cmd unroll_i c2 in
      ([:: MkI ii (Cif b c1' c2') ], b1 || b2)
  | Cfor i (dir, low, hi) c =>
    let: (c', b) := unroll_cmd unroll_i c in
    match is_const low, is_const hi with
    | Some vlo, Some vhi =>
      let l := wrange dir vlo vhi in
      let cs := map (fun n => assgn ii i (Pconst n) :: c') l in
      (flatten cs, true)
    | _, _       => ([:: MkI ii (Cfor i (dir, low, hi) c') ], b)
    end
  | Cwhile a c1 e c2  =>
      let: (c1', b1) := unroll_cmd unroll_i c1 in
      let: (c2', b2) := unroll_cmd unroll_i c2 in
      ([:: MkI ii (Cwhile a c1' e c2') ], b1 || b2)
  end.

Section Section.

Context {pT: progT}.

Definition unroll_fun (f: fun_decl) :=
  let: (fn, MkFun ii si p c so r ev) := f in
  let: (c', b) := unroll_cmd unroll_i c in
  ((fn, MkFun ii si p c' so r ev), b).

Definition unroll_prog (p: prog) : prog * bool :=
  let: (fds, b) := map_repeat unroll_fun (p_funcs p) in
  ({| p_funcs := fds ; p_globs := p_globs p ; p_extra := p_extra p |}, b).

End Section.

End ASM_OP.
