(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
From CoqWord Require Import ssrZ.
Require Import compiler_util expr ZArith.
Import all_ssreflect.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* -------------------------------------------------------------------------- *)
(* ** Data structure used for the analisys                                    *)
(* -------------------------------------------------------------------------- *)

Record pimap := {
   pi_defs : Mvar.t (pexpr * Sv.t);  (* pi_defs[x] = (e, read_e e), e is the value associate to x *)
   pi_used : Mvar.t Sv.t;      (* pi_used[x] = xs, xs is the variables depending on x *)
}.

Definition piempty := 
  {| pi_defs := Mvar.empty _
   ; pi_used := Mvar.empty _ |}.

Definition get (pi:pimap) (x:var) := 
  Mvar.get pi.(pi_defs) x.

Definition on_used (f : Sv.t -> Sv.t) (fv:Sv.t) used :=
  Sv.fold (fun y u => 
                let xs := f (odflt Sv.empty (Mvar.get u y)) in
                Mvar.set u y xs) fv used.

Definition remove (pi:pimap) (x:var) := 
  match get pi x with
  | None => pi
  | Some (_, fv) =>
    let used := on_used (Sv.remove x) fv pi.(pi_used) in
    {| pi_defs := Mvar.remove pi.(pi_defs) x
     ; pi_used := used |}
  end.

Definition set (pi:pimap) (x:var) (e:pexpr) := 
  let fv := read_e e in
  let used := on_used (Sv.add x) fv pi.(pi_used) in
  {| pi_defs := Mvar.set pi.(pi_defs) x (e,fv) 
   ; pi_used := used |}.

Definition merge (pi1 pi2:pimap) := 
  let ondefs (_:var) (o1 o2 : option (pexpr * Sv.t)) := 
    match o1, o2 with
    | Some (e1,_), Some (e2, _) => 
      if eq_expr e1 e2 then o1
      else None
    | _, _ => None
    end in
  let onused (_:var) (o1 o2 : option Sv.t) := 
    match o1, o2 with
    | Some xs1, Some xs2 => Some (Sv.inter xs1 xs2)
    | _, _ => None
    end in  
  {| pi_defs := Mvar.map2 ondefs pi1.(pi_defs) pi2.(pi_defs)
   ; pi_used := Mvar.map2 onused pi1.(pi_used) pi2.(pi_used) |}.

Definition incl (pi1 pi2:pimap) := 
  Mvar.incl (fun _ efv1 efv2 => eq_expr efv1.1 efv2.1) pi1.(pi_defs) pi2.(pi_defs)&&
  Mvar.incl (fun _ s1 s2 => Sv.subset s1 s2) pi1.(pi_used) pi2.(pi_used).
  
(* -------------------------------------------------------------------------- *)
(* ** Transformation                                                          *)
(* -------------------------------------------------------------------------- *)

Fixpoint pi_e (pi:pimap) (e:pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => e 
  | Pvar x => 
    if is_lvar x then
      match get pi x.(gv) with
      | Some (e', _) => e'
      | None => e 
      end 
    else e
  | Pget aa ws x e     => Pget aa ws x (pi_e pi e)
  | Psub aa ws len x e => Psub aa ws len x (pi_e pi e)
  | Pload ws x e       => Pload ws x (pi_e pi e)
  | Papp1 o e          => Papp1 o (pi_e pi e)
  | Papp2 o e1 e2      => Papp2 o (pi_e pi e1) (pi_e pi e2)
  | PappN o es         => PappN o (map (pi_e pi) es)
  | Pif t e e1 e2      => Pif t (pi_e pi e) (pi_e pi e1) (pi_e pi e2)
  end.

Definition pi_es (pi:pimap) (es:pexprs) := 
  map (pi_e pi) es.

Definition pi_lv (pi:pimap) (lv:lval) :=
  match lv with
  | Lnone _ _           => (pi, lv) 
  | Lvar x              => (remove pi x, lv)
  | Lmem ws x e         => (pi, Lmem ws x (pi_e pi e))
  | Laset aa ws x e     => (remove pi x, Laset aa ws x (pi_e pi e))
  | Lasub aa ws len x e => (remove pi x, Lasub aa ws len x (pi_e pi e))
  end. 
  
(* TODO: move this in utils use it in constant_prop.const_prop_rvs ... *)
Section MF.
  Context (A B C:Type) (f : A -> B -> A * C).

  Fixpoint map_fold (a:A) (lb:list B) : A * list C := 
    match lb with
    | [::] => (a, [::])
    | b::lb => 
      let (a, c) := f a b in
      let (a, lc) := map_fold a lb in
      (a, c :: lc)
    end.

End MF.

Definition pi_lvs (pi:pimap) (xs:lvals) := map_fold pi_lv pi xs.

Definition set_lv (pi:pimap) x tag ty (e:pexpr) :=
  if x is Lvar x then
    if (tag == AT_inline) && (x.(vtype) == ty) then set pi x e
    else pi
  else pi.

Section LOOP.

  Context (pi_i : pimap -> instr -> ciexec (pimap * instr)). 

  (* TODO: add map_foldM in utils *)
  Fixpoint pi_c (pi:pimap) (c:cmd) := 
    match c with
    | [::] => ok (pi, [::])
    | i::c => 
      Let pii := pi_i pi i in 
      Let pic := pi_c pii.1 c in
      ok (pic.1, pii.2 :: pic.2)
    end.

  Context (ii:instr_info).
  Context (x:var) (c:cmd).

  Fixpoint loop_for (n:nat) (pi:pimap)  :=
    match n with
    | O => cierror ii (Cerr_Loop "propagate_inline")
    | S n =>
      let pii := remove pi x in
      Let pic := pi_c pii c in
      if incl pi pic.1 then ok (pi, pic.2)
      else loop_for n (merge pi pic.1)
    end.

  Context (c1:cmd) (e:pexpr) (c2:cmd).

  Fixpoint loop_while (n:nat) (pi:pimap) :=
    match n with
    | O => cierror ii (Cerr_Loop "propagate_inline")
    | S n =>
      (* c1; while e do c2; c1 *)
      Let pic1 := pi_c pi c1 in
      Let pic2 := pi_c pic1.1 c2 in
      if incl pi pic2.1 then ok (pic1.1, pic1.2, pi_e pic1.1 e, pic2.2)
      else loop_while n pi  
    end.

End LOOP.

Fixpoint pi_i (pi:pimap) (i:instr) := 
  let (ii, ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    let e := pi_e pi e in
    let (pi, x) := pi_lv pi x in 
    let pi := set_lv pi x tag ty e in
    ok (pi, MkI ii (Cassgn x tag ty e))

  | Copn xs tag o es => 
    let es := pi_es pi es in
    let (pi, xs) := pi_lvs pi xs in
    ok (pi, MkI ii (Copn xs tag o es))

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

  | Ccall inline xs f es =>
    let es := pi_es pi es in
    let (pi, xs) := pi_lvs pi xs in
    ok (pi, MkI ii (Ccall inline xs f es))

  end.

Section Section.

Context {T} {pT:progT T}.

Definition pi_fun  (f:fundef) :=
  let 'MkFun ii si p c so r ev := f in
  Let pic := pi_c pi_i piempty c in 
  ok (MkFun ii si p pic.2 so r ev).

Definition pi_prog (p:prog) := 
  Let funcs := map_cfprog pi_fun (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.



