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
From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "dead code".

  Definition ii_loop_iterator := ii_loop_iterator pass.

  Definition dead_code_error := pp_internal_error_s pass.

End E.

Section ASM_OP.

Context `{asmop : asmOp}.

Definition dead_code_c (dead_code_i: instr -> Sv.t -> cexec (Sv.t * cmd))
                       c s :  cexec (Sv.t * cmd):=
  foldr (fun i r =>
    Let r := r in
    Let ri := dead_code_i i r.1 in
    ok (ri.1, ri.2 ++ r.2)) (ok (s,[::])) c.

Section LOOP.

  Variable dead_code_c : Sv.t -> cexec (Sv.t * cmd).
  Variable dead_code_c2 : Sv.t -> cexec (Sv.t * (Sv.t * (cmd*cmd))).
  Variable ii : instr_info.

  Fixpoint loop (n:nat) (rx:Sv.t) (wx:Sv.t) (s:Sv.t) : cexec (Sv.t * cmd) :=
    match n with
    | O => Error (ii_loop_iterator ii)
    | S n =>
      Let sc := dead_code_c s in
      let: (s',c') := sc in
      let s' := Sv.union rx (Sv.diff s' wx) in
      if Sv.subset s' s then ok (s,c')
      else loop n rx wx (Sv.union s s')
    end.

  Fixpoint wloop (n:nat) (s:Sv.t) : cexec (Sv.t * (cmd * cmd)) :=
    match n with
    | O => Error (ii_loop_iterator ii)
    | S n =>
      Let sc := dead_code_c2 s in
      let: (s',sic) := sc in
      if Sv.subset s' s then ok sic
      else wloop n (Sv.union s s')
    end.

End LOOP.

(* Architecture-dependent check that an op is a move *)
Context (is_move_op : asm_op_t -> bool).

Definition check_nop (rv:lval) (e:pexpr) :=
  match rv, e with
  | Lvar x1, Pvar x2 => is_lvar x2 && (x1.(v_var) == x2.(gv).(v_var))
  | _, _ => false
  end.

Definition check_nop_opn (xs:lvals) (o: sopn) (es:pexprs) :=
  match xs, o, es with
  | [:: x], Oasm op, [:: e] => is_move_op op && check_nop x e
  | _, _, _ => false
  end.

Fixpoint keep_only {T:Type} (l:seq T) (tokeep : seq bool) {struct tokeep}:= 
  match tokeep, l with
  | [::], _ => l 
  | b::tokeep, [::] => [::]
  | b::tokeep, x::l => 
    let l := keep_only l tokeep in 
    if b then x::l else l
  end.

Section ONFUN.

Context (do_nop: bool) (onfun: funname -> option (seq bool)).

Definition fn_keep_only {T:Type} (fn:funname) (l:seq T) := 
  match onfun fn with
  | None => l
  | Some tokeep => keep_only l tokeep
  end.

(* TODO: could be written using [fmapM2] I think. Is it worth it? *)
(* FIXME: initially, it was a linear error, why? *)
Fixpoint check_keep_only (xs:lvals) (tokeep: seq bool) s : cexec (Sv.t * lvals) :=
  match tokeep, xs with
  | [::], [::] => ok (s, [::])
  | b::tokeep, x::xs =>
    Let sxs := check_keep_only xs tokeep s in
    let '(s,xs) := sxs in
    if b then
      ok (read_rv_rec (Sv.diff s (vrv x)) x, x::xs)
    else
      let w := vrv x in
      if disjoint s w && negb (lv_write_mem x) then ok (s, xs)
      else Error (dead_code_error "check_keep_only")
  | _, _ => Error (dead_code_error "check_keep_only invalid size")
  end.

Fixpoint dead_code_i (i:instr) (s:Sv.t) {struct i} : cexec (Sv.t * cmd) :=
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    let w := write_i ir in
    if tag != AT_keep then
      if (disjoint s w && negb (lv_write_mem x)) || 
         ((do_nop || (tag == AT_rename)) && check_nop x e) then ok (s, [::])
      else ok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ])
    else   ok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ])

  | Copn xs tag o es =>
    let w := vrvs xs in
    if tag != AT_keep then
      if disjoint s w && negb (has lv_write_mem xs) then ok (s, [::])
      else if check_nop_opn xs o es then ok (s, [::])
      else ok (read_es_rec (read_rvs_rec (Sv.diff s w) xs) es, [:: i])
    else   ok (read_es_rec (read_rvs_rec (Sv.diff s w) xs) es, [:: i])

  | Cif b c1 c2 =>
    Let sc1 := dead_code_c dead_code_i c1 s in
    Let sc2 := dead_code_c dead_code_i c2 s in
    let: (s1,c1) := sc1 in
    let: (s2,c2) := sc2 in
    ok (read_e_rec (Sv.union s1 s2) b, [:: MkI ii (Cif b c1 c2)])

  | Cfor x (dir, e1, e2) c =>
    Let sc := loop (dead_code_c dead_code_i c) ii Loop.nb
                   (read_rv (Lvar x)) (vrv (Lvar x)) s in
    let: (s, c) := sc in
    ok (read_e_rec (read_e_rec s e2) e1,[:: MkI ii (Cfor x (dir,e1,e2) c) ])

  | Cwhile a c e c' =>
    let dobody s_o :=
      let s_o' := read_e_rec s_o e in
      Let sci := dead_code_c dead_code_i c s_o' in
      let: (s_i, c) := sci in
      Let sci' := dead_code_c dead_code_i c' s_i in
      let: (s_i', c') := sci' in
      ok (s_i', (s_i, (c,c'))) in
    Let sc := wloop dobody ii Loop.nb s in
    let: (s, (c,c')) := sc in
    ok (s, [:: MkI ii (Cwhile a c e c') ])

  | Ccall ini xs fn es =>
    Let sxs := 
      match onfun fn with
      | None => ok (read_rvs_rec (Sv.diff s (vrvs xs)) xs, xs)
      | Some bs => add_iinfo ii (check_keep_only xs bs s)
      end in
    let '(si,xs) := sxs in
    ok (read_es_rec si es, [:: MkI ii (Ccall ini xs fn es)])

  end.

Section Section.

Context {T} {pT:progT T}.

Definition dead_code_fd {eft} fn (fd: _fundef eft) : cexec (_fundef eft) :=
  let 'MkFun ii tyi params c tyo res ef := fd in
  let res := fn_keep_only fn res in
  let tyo := fn_keep_only fn tyo in
  let s := read_es (map Plvar res) in
  Let c := dead_code_c dead_code_i c s in
  ok (MkFun ii tyi params c.2 tyo res ef).

Definition dead_code_prog_tokeep (p: prog) : cexec prog :=
  Let funcs := map_cfprog_name dead_code_fd (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.

End ONFUN.

Definition dead_code_prog {T} {pT:progT T} (p:prog) do_nop :=
  @dead_code_prog_tokeep do_nop (fun _ => None) T pT p.

End ASM_OP.
