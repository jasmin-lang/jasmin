(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.
Require Import compiler_util expr ZArith constant_prop.
Require Import
  flag_combination.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Import E.

  Definition pass : string := "propagate inline".

  Definition ii_loop_iterator := ii_loop_iterator pass.

End E.

(* -------------------------------------------------------------------------- *)
(* ** Data structure used for the analisys                                    *)
(* -------------------------------------------------------------------------- *)

Record pi_cel := { 
  pi_def : pexpr; (* associate expression *)
  pi_fv  : Sv.t;  (* read_e pi_def        *)
  pi_m   : bool;  (* use_mem pi_def       *) 
  pi_fv_ok : pi_fv = read_e pi_def;
  pi_m_ok  : pi_m = use_mem pi_def;
}.

Definition pimap := Mvar.t pi_cel. 

Definition piempty : pimap := Mvar.empty _.

Definition remove (pi:pimap) (x:var) := 
  Mvar.filter_map (fun y c => if (x == y) || Sv.mem x c.(pi_fv) then None else Some c) pi.

Definition remove_m (pi:pimap) := 
  Mvar.filter_map (fun y c => if c.(pi_m) then None else Some c) pi.

Definition set (pi:pimap) (x:var) (e:pexpr) := 
  let fv := read_e e in
  let use := use_mem e in
  if Sv.mem x fv then pi
  else 
    Mvar.set pi x {| pi_def := e; pi_fv_ok := erefl fv; pi_m_ok := erefl use |}.

Definition merge (pi1 pi2:pimap) := 
  let ondefs (_:var) (o1 o2 : option pi_cel) := 
    match o1, o2 with
    | Some c1, Some c2 => 
      if eq_expr c1.(pi_def) c2.(pi_def) then o1
      else None
    | _, _ => None
    end in
  Mvar.map2 ondefs pi1 pi2.
  
Definition incl (pi1 pi2:pimap) := 
  Mvar.incl (fun _ c1 c2 => eq_expr c1.(pi_def) c2.(pi_def)) pi1 pi2.

(* -------------------------------------------------------------------------- *)
(* ** Transformation                                                          *)
(* -------------------------------------------------------------------------- *)

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {asmop:asmOp asm_op}
  {fcp : FlagCombinationParams}.

Definition scfc (cf : combine_flags) (es : seq pexpr) : pexpr :=
  if es is [:: eof; ecf; esf; ezf ]
  then cf_xsem snot sand sor sbeq eof ecf esf ezf cf
  else PappN (Ocombine_flags cf) es. (* Never happens. *)

Fixpoint pi_e (pi:pimap) (e:pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => e 
  | Pvar x => 
    if is_lvar x then
      match Mvar.get pi x.(gv) with
      | Some c => c.(pi_def)
      | None => e 
      end 
    else e
  | Pget al aa ws x e  => Pget al aa ws x (pi_e pi e)
  | Psub aa ws len x e => Psub aa ws len x (pi_e pi e)
  | Pload al ws x e    => Pload al ws x (pi_e pi e)
  | Papp1 o e          => Papp1 o (pi_e pi e)
  | Papp2 o e1 e2      => Papp2 o (pi_e pi e1) (pi_e pi e2)
  | PappN o es         => 
    let es := (map (pi_e pi) es) in
    match o with
    | Opack _ _ => PappN o es
    | Ocombine_flags c => scfc c es
    end
  | Pif t e e1 e2      => Pif t (pi_e pi e) (pi_e pi e1) (pi_e pi e2)
  end.

Definition pi_es (pi:pimap) (es:pexprs) := 
  map (pi_e pi) es.

Definition pi_lv (pi:pimap) (lv:lval) :=
  match lv with
  | Lnone _ _           => (pi, lv) 
  | Lvar x              => (remove pi x, lv)
  | Lmem al ws x e      => (remove_m pi, Lmem al ws x (pi_e pi e))
  | Laset al aa ws x e  => (remove pi x, Laset al aa ws x (pi_e pi e))
  | Lasub aa ws len x e => (remove pi x, Lasub aa ws len x (pi_e pi e))
  end.

Definition pi_lvs (pi:pimap) (xs:lvals) := fmap pi_lv pi xs.

Definition set_lv (pi:pimap) x tag (e:pexpr) :=
  if x is Lvar x then
    if tag == AT_inline then set pi x e
    else pi
  else pi.

Section LOOP.

  Context (pi_i : pimap -> instr -> cexec (pimap * instr)).

  Definition pi_c := fmapM pi_i.

  Context (ii:instr_info).
  Context (x:var) (c:cmd).

  Fixpoint loop_for (n:nat) (pi:pimap)  :=
    match n with
    | O => Error (E.ii_loop_iterator ii)
    | S n =>
      let pii := remove pi x in
      Let pic := pi_c pii c in
      if incl pi pic.1 then ok (pi, pic.2)
      else loop_for n (merge pi pic.1)
    end.

  Context (c1:cmd) (e:pexpr) (c2:cmd).

  Fixpoint loop_while (n:nat) (pi:pimap) :=
    match n with
    | O => Error (E.ii_loop_iterator ii)
    | S n =>
      (* c1; while e do c2; c1 *)
      Let pic1 := pi_c pi c1 in
      Let pic2 := pi_c pic1.1 c2 in
      if incl pi pic2.1 then ok (pic1.1, pic1.2, pi_e pic1.1 e, pic2.2)
      else loop_while n (merge pi pic2.1) 
    end.

End LOOP.

Fixpoint pi_i (pi:pimap) (i:instr) := 
  let (ii, ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    let e := pi_e pi e in
    let (pi, x) := pi_lv pi x in 
    let pi := set_lv pi x tag e in
    ok (pi, MkI ii (Cassgn x tag ty e))

  | Copn xs tag o es => 
    let es := pi_es pi es in
    let (pi, xs) := pi_lvs pi xs in
    ok (pi, MkI ii (Copn xs tag o es))

  | Csyscall xs o es =>
    let es := pi_es pi es in
    (* Remark: for uprog it is not necessary *)
    let pi := remove_m pi in
    let (pi, xs) := pi_lvs pi xs in
    ok (pi, MkI ii (Csyscall xs o es))

  | Cif e c1 c2 => 
    let e := pi_e pi e in
    Let pic1 := pi_c pi_i pi c1 in
    Let pic2 := pi_c pi_i pi c2 in
    let pi := merge pic1.1 pic2.1 in
    ok (pi, MkI ii (Cif e pic1.2 pic2.2))

  | Cfor x (d,e1,e2) c => 
    let e1 := pi_e pi e1 in
    let e2 := pi_e pi e2 in
    Let pic := loop_for pi_i ii x c Loop.nb pi in
    ok (pic.1, MkI ii (Cfor x (d,e1,e2) pic.2))
    
  | Cwhile a c1 e c2 => 
    Let pic := loop_while pi_i ii c1 e c2 Loop.nb pi in
    let:(pi, c1, e, c2) := pic in
    ok (pi, MkI ii (Cwhile a c1 e c2))

  | Ccall xs f es =>
    let es := pi_es pi es in
    let (pi, xs) := pi_lvs (remove_m pi) xs in
    ok (pi, MkI ii (Ccall xs f es))

  end.

Section Section.

Context {pT:progT}.

Definition pi_fun  (f:fundef) :=
  let 'MkFun ii si p c so r ev := f in
  Let pic := pi_c pi_i piempty c in 
  ok (MkFun ii si p pic.2 so r ev).

Definition pi_prog (p:prog) := 
  Let funcs := map_cfprog pi_fun (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.

End WITH_PARAMS.
