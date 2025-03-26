(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import expr sem_op_typed compiler_util.
Import Utf8.
Import oseq.
Require Import flag_combination.

Local Open Scope seq_scope.
Local Open Scope Z_scope.


Section WITH_PARAMS.

Context {fcp : FlagCombinationParams}.

Definition e2bool (e:pexpr) : exec bool :=
  match e with
  | Pbool b => ok b
  | _       => type_error
  end.

Definition e2int (e:pexpr) : exec Z :=
  match e with
  | Pconst z => ok z
  | _        => type_error
  end.

Definition e2word (sz:wsize) (e:pexpr) : exec (word sz) :=
  match is_wconst sz e with
  | Some w => ok w
  | None   => type_error
  end.

Definition of_expr (t:stype) : pexpr -> exec (sem_t t) :=
  match t return pexpr -> exec (sem_t t) with
  | sbool   => e2bool
  | sint    => e2int
  | sarr n  => fun _ => type_error
  | sword sz => e2word sz
  | sabstract _ => fun _ => type_error
  end.

Definition to_expr (t:stype) : sem_t t -> exec pexpr :=
  match t return sem_t t -> exec pexpr with
  | sbool => fun b => ok (Pbool b)
  | sint  => fun z => ok (Pconst z)
  | sarr _ => fun _ => type_error
  | sword sz => fun w => ok (wconst w)
  | sabstract _ => fun _ => type_error
  end.

Definition ssem_sop1 (o: sop1) (e: pexpr) : pexpr :=
  let r :=
    Let x := of_expr _ e in
    to_expr (sem_sop1_typed o x) in
  match r with
  | Ok e => e
  | _ => Papp1 o e
  end.

Definition ssem_sop2 (o: sop2) (e1 e2: pexpr) : pexpr :=
  let r :=
    Let x1 := of_expr _ e1 in
    Let x2 := of_expr _ e2 in
    Let v  := sem_sop2_typed o x1 x2 in
    to_expr v in
  match r with
  | Ok e => e
  | _ => Papp2 o e1 e2
  end.

(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Fixpoint snot (e:pexpr) :=
  match e with
  | Pbool b      => ~~b
  | Papp1 Onot e => e
  | Papp2 Oand e1 e2 => Papp2 Oor (snot e1) (snot e2)
  | Papp2 Oor  e1 e2 => Papp2 Oand (snot e1) (snot e2)
  | Pif t e e1 e2 => Pif t e (snot e1) (snot e2)
  | _             => Papp1 Onot e
  end.

Definition sneg_int (e: pexpr) :=
  match e with
  | Pconst z => Pconst (- z)
  | Papp1 (Oneg Op_int) e' => e'
  | _ => Papp1 (Oneg Op_int) e
  end.

Definition s_op1 o e :=
  match o with
  | Onot        => snot e
  | Oneg Op_int => sneg_int e
  | _           => ssem_sop1 o e
  end.

(* ------------------------------------------------------------------------ *)

Definition sbeq e1 e2 :=
  match is_bool e1, is_bool e2 with
  | Some b1, Some b2 => Pbool (b1 == b2)
  | Some b, _ => if b then e2 else snot e2
  | _, Some b => if b then e1 else snot e1
  | _, _      => Papp2 Obeq e1 e2
  end.

Definition sand e1 e2 :=
  match is_bool e1, is_bool e2 with
  | Some b, _ => if b then e2 else false
  | _, Some b => if b then e1 else false
  | _, _      => Papp2 Oand e1 e2
  end.

Definition sor e1 e2 :=
   match is_bool e1, is_bool e2 with
  | Some b, _ => if b then Pbool true else e2
  | _, Some b => if b then Pbool true else e1
  | _, _       => Papp2 Oor e1 e2
  end.

(* ------------------------------------------------------------------------ *)

Definition sadd_int e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 + n2)
  | Some n, _ =>
    if (n == 0)%Z then e2 else Papp2 (Oadd Op_int) e1 e2
  | _, Some n =>
    if (n == 0)%Z then e1 else Papp2 (Oadd Op_int) e1 e2
  | _, _ => Papp2 (Oadd Op_int) e1 e2
  end.

Definition sadd_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => wconst (n1 + n2)
  | Some n, _ => if n == 0%R then e2 else Papp2 (Oadd (Op_w sz)) e1 e2
  | _, Some n => if n == 0%R then e1 else Papp2 (Oadd (Op_w sz)) e1 e2
  | _, _ => Papp2 (Oadd (Op_w sz)) e1 e2
  end.

Definition sadd ty :=
  match ty with
  | Op_int => sadd_int
  | Op_w sz => sadd_w sz
  end.

Definition ssub_int e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 - n2)
  | _, Some n =>
    if (n == 0)%Z then e1 else Papp2 (Osub Op_int) e1 e2
  | _, _ => Papp2 (Osub Op_int) e1 e2
  end.

Definition ssub_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => wconst (n1 - n2)
  | _, Some n => if n == 0%R then e1 else Papp2 (Osub (Op_w sz)) e1 e2
  | _, _ => Papp2 (Osub (Op_w sz)) e1 e2
  end.

Definition ssub ty :=
  match ty with
  | Op_int => ssub_int
  | Op_w sz => ssub_w sz
  end.

Definition smul_int e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 * n2)
  | Some n, _ =>
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e2
    else Papp2 (Omul Op_int) e1 e2
  | _, Some n =>
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e1
    else Papp2 (Omul Op_int) e1 e2
  | _, _ => Papp2 (Omul Op_int) e1 e2
  end.

Definition smul_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => wconst (n1 * n2)
  | Some n, _ =>
    if n == 0%R then @wconst sz 0
    else if n == 1%R then e2
    else Papp2 (Omul (Op_w sz)) (wconst n) e2
  | _, Some n =>
    if n == 0%R then @wconst sz 0
    else if n == 1%R then e1
    else Papp2 (Omul (Op_w sz)) e1 (wconst n)
  | _, _ => Papp2 (Omul (Op_w sz)) e1 e2
  end.

Definition smul ty :=
  match ty with
  | Op_int => smul_int
  | Op_w sz => smul_w sz
  end.

Definition s_eq ty e1 e2 :=
  if eq_expr e1 e2 then Pbool true
  else
    match ty with
    | Op_int =>
      match is_const e1, is_const e2 with
      | Some i1, Some i2 => Pbool (i1 == i2)
      | _, _             => Papp2 (Oeq ty) e1 e2
      end
    | Op_w sz =>
      match is_wconst sz e1, is_wconst sz e2 with
      | Some i1, Some i2 => Pbool (i1 == i2)
      | _, _             => Papp2 (Oeq ty) e1 e2
      end
    end.

Definition sneq ty e1 e2 :=
  match is_bool (s_eq ty e1 e2) with
  | Some b => Pbool (~~ b)
  | None      => Papp2 (Oneq ty) e1 e2
  end.

Definition is_cmp_const (ty: cmp_kind) (e: pexpr) : option Z :=
  match ty with
  | Cmp_int => is_const e
  | Cmp_w sg sz =>
    is_wconst sz e >>= λ w,
    Some match sg with
    | Signed => wsigned w
    | Unsigned => wunsigned w
    end
  end%O.

Definition slt ty e1 e2 :=
  if eq_expr e1 e2 then Pbool false
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => Pbool (n1 <? n2)%Z
  | _      , _       => Papp2 (Olt ty) e1 e2
  end.

Definition sle ty e1 e2 :=
  if eq_expr e1 e2 then Pbool true
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => Pbool (n1 <=? n2)%Z
  | _      , _       => Papp2 (Ole ty) e1 e2
  end.

Definition sgt ty e1 e2 :=
  if eq_expr e1 e2 then Pbool false
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => Pbool (n1 >? n2)%Z
  | _      , _       => Papp2 (Ogt ty) e1 e2
  end.

Definition sge ty e1 e2 :=
  if eq_expr e1 e2 then Pbool true
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => Pbool (n1 >=? n2)%Z
  | _      , _       => Papp2 (Oge ty) e1 e2
  end.


Definition s_op2 o e1 e2 :=
  match o with
  | Obeq    => sbeq e1 e2
  | Oand    => sand e1 e2
  | Oor     => sor  e1 e2
  | Oadd ty => sadd ty e1 e2
  | Osub ty => ssub ty e1 e2
  | Omul ty => smul ty e1 e2
  | Oeq  ty => s_eq ty e1 e2
  | Oneq ty => sneq ty e1 e2
  | Olt  ty => slt  ty e1 e2
  | Ole  ty => sle  ty e1 e2
  | Ogt  ty => sgt  ty e1 e2
  | Oge  ty => sge  ty e1 e2
  | _       => ssem_sop2 o e1 e2
  end.

Definition app_sopn := app_sopn of_expr.

Arguments app_sopn {A} ts _ _.

Definition s_opN (op:opN) (es:pexprs) : pexpr :=
  match app_sopn _ (sem_opN_typed op) es with
  | Ok r =>
    match op return sem_t (type_of_opN op).2 -> _ with
    | Opack ws _ => fun w => Papp1 (Oword_of_int ws) (Pconst (wunsigned w))
    | Ocombine_flags _ => fun b => Pbool b
    end r
  | _ => pappN op es
  end.

Definition s_opNA (op:opNA) (es:pexprs) : pexpr :=
  match op with
  | OopN o => s_opN o es
  | Oabstract _ => PappN op es
  end.

Definition s_if t e e1 e2 :=
  match is_bool e with
  | Some b => if b then e1 else e2
  | None   => Pif t e e1 e2
  end.

(* ** constant propagation
 * -------------------------------------------------------------------- *)

Variant const_v :=
  | Cbool of bool
  | Cint of Z
  | Cword sz `(word sz).

Definition const_v_beq (c1 c2: const_v) : bool :=
  match c1, c2 with
  | Cbool b1, Cbool b2 => b1 == b2
  | Cint z1, Cint z2 => z1 == z2
  | Cword sz1 w1, Cword sz2 w2 =>
    match wsize_eq_dec sz1 sz2 with
    | left e => eq_rect _ word w1 _ e == w2
    | _ => false
    end
  | _, _ => false
  end.

Lemma const_v_eq_axiom : Equality.axiom const_v_beq.
Proof.
case => [ b1 | z1 | sz1 w1 ] [ b2 | z2 | sz2 w2] /=; try (constructor; congruence).
+ case: eqP => [ -> | ne ]; constructor; congruence.
+ case: eqP => [ -> | ne ]; constructor; congruence.
case: wsize_eq_dec => [ ? | ne ]; last (constructor; congruence).
subst => /=.
by apply:(iffP idP) => [ /eqP | [] ] ->.
Qed.

HB.instance Definition _ := hasDecEq.Build const_v const_v_eq_axiom.

Local Notation cpm := (Mvar.t const_v).

Definition const v :=
  match v with
  | Cbool b => Pbool b
  | Cint z  => Pconst z
  | Cword sz z => wconst z
  end.

Definition globals : Type := option (var → option glob_value).

Let without_globals : globals := None.
Let with_globals (gd: glob_decls) (tag: assgn_tag) : globals :=
  if tag is AT_inline then Some (assoc gd) else None.




Section GLOBALS.

Context (globs: globals).




Let pget_global al aa sz x e : pexpr :=
  if globs is Some f then if f x.(gv) is Some (Garr len a) then if e is Pconst i then if WArray.get al aa sz a i is Ok w then wconst w
  else Pget al aa sz x e
  else Pget al aa sz x e
  else Pget al aa sz x e
  else Pget al aa sz x e.

Fixpoint const_prop_e (m:cpm) e  :=
  match e with
  | Pconst _
  | Pbool  _
  | Parr_init _
    => e
  | Pvar {| gs := scope ; gv := x |} =>
      match scope with
      | Slocal => if Mvar.get m x is Some n then const n else e
      | Sglob => if globs is Some f then if f x is Some (Gword ws w) then const (Cword w) else e else e
      end
  | Pget al aa sz x e =>
      let e := const_prop_e m e in
      if is_glob x
      then pget_global al aa sz x e
      else Pget al aa sz x e
  | Psub aa sz len x e => Psub aa sz len x (const_prop_e m e)
  | Pload al sz x e  => Pload al sz x (const_prop_e m e)
  | Papp1 o e     => s_op1 o (const_prop_e m e)
  | Papp2 o e1 e2 => s_op2 o (const_prop_e m e1)  (const_prop_e m e2)
  | PappN op es   => s_opNA op (map (const_prop_e m) es)
  | Pif t e e1 e2 => s_if t (const_prop_e m e) (const_prop_e m e1) (const_prop_e m e2)
  | Pbig idx op x body s len =>
     let s   := const_prop_e m s in
     let len := const_prop_e m len in
     let idx := const_prop_e m idx in
     match is_const s, is_const len with
     | Some s, Some len =>
       foldl (fun acc i =>
               let m := Mvar.set m x (Cint i) in
               let b := const_prop_e m body in
               Papp2 op acc b)
             idx (ziota s len)
     | _, _ =>
         Pbig idx op x (const_prop_e (Mvar.remove m x) body) s len
     end

   | Pis_var_init _ => e

   | Pis_arr_init x e1 e2 =>
     let e1 := const_prop_e m e1 in
     let e2 := const_prop_e m e2 in
     Pis_arr_init x e1 e2

   | Pis_mem_init e1 e2 =>
     let e1 := const_prop_e m e1 in
     let e2 := const_prop_e m e2 in
     Pis_mem_init e1 e2

  end.

End GLOBALS.

Definition empty_cpm : cpm := @Mvar.empty const_v.

Definition empty_const_prop_e := const_prop_e without_globals empty_cpm.

Definition merge_cpm : cpm -> cpm -> cpm :=
  Mvar.map2 (fun _ (o1 o2: option const_v) =>
   match o1, o2 with
   | Some n1, Some n2 =>
     if (n1 == n2)%Z then Some n1
     else None
   | _, _ => None
   end).

Definition includes_cpm (m1:cpm) (m2:cpm): bool :=
  Mvar.fold (fun x n1 b =>
    match Mvar.get m2 x with
    | Some n2 => (n1 == n2)%Z && b
    | None => true
    end) m1 true.



Definition remove_cpm (m:cpm) (s:Sv.t): cpm :=
  Sv.fold (fun x m => Mvar.remove m x) s m.

Definition const_prop_rv globs (m:cpm) (rv:lval) : cpm * lval :=
  match rv with
  | Lnone _ _       => (m, rv)
  | Lvar  x         => (Mvar.remove m x, rv)
  | Lmem al sz x e  => (m, Lmem al sz x (const_prop_e globs m e))
  | Laset al aa sz x e => (Mvar.remove m x, Laset al aa sz x (const_prop_e globs m e))
  | Lasub aa sz len x e => (Mvar.remove m x, Lasub aa sz len x (const_prop_e globs m e))
  end.

Fixpoint const_prop_rvs globs (m:cpm) (rvs:lvals) : cpm * lvals :=
  match rvs with
  | [::] => (m, [::])
  | rv::rvs =>
    let (m,rv)  := const_prop_rv globs m rv in
    let (m,rvs) := const_prop_rvs globs m rvs in
    (m, rv::rvs)
  end.

Definition wsize_of_stype (ty: stype) : wsize :=
  if ty is sword sz then sz else U64.

Section LOOP.
  Context `{asmop : asmOp}.

  Variable cp_c2 : cpm ->  cpm * (cpm * (cmd*cmd)).

  Variable wloop_fallback: cpm * (cmd * cmd).

  
  Fixpoint wloop (n:nat) (m:cpm) :=
    match n with
    | O => wloop_fallback
    | S n => 
      let: (m2,(m1,cs)) := cp_c2 m in
      if includes_cpm m2 m then (m1,cs) 
      else wloop n (merge_cpm m2 m)
    end.

End LOOP.


Section ASM_OP.

Context {msfsz : MSFsize} `{asmop:asmOp}.

Section CMD.


Definition add_cpm (m:cpm) (rv:lval) (tag:assgn_tag) e cpf ty :=
if rv is Lvar x then
  if cpf rv tag e then
    match e with
    | Pbool b  => Mvar.set m x (Cbool b)
    | Pconst z =>  Mvar.set m x (Cint z)
    | Papp1 (Oword_of_int _) (Pconst z) =>
      let szty := wsize_of_stype ty in
      let szx := wsize_of_stype (vtype x) in
      let sz := cmp_min szty szx in
      let w := Cword (wrepr sz z) in
      Mvar.set m x w
    | _ => m
    end
  else m
else m.

  Variable const_prop_i : cpm -> instr -> cpm * cmd.

  Fixpoint const_prop (m:cpm) (c:cmd) : cpm * cmd :=
    match c with
    | [::] => (m, [::])
    | i::c =>
      let (m,ic) := const_prop_i m i in
      let (m, c) := const_prop m c in
      (m, ic ++ c)
    end.

End CMD.

Definition is_update_imm (xs:lvals) o es :=
  match o, es, xs with
  | Oslh SLHupdate, [:: Pbool b; e], [:: x] => Some (x, b, e)
  | _, _, _=> None
  end.

Section GLOBALS.

Context (gd: glob_decls).

Fixpoint const_prop_ir with_globals without_globals cpf (m:cpm) ii (ir:instr_r) : cpm * cmd :=
  let const_prop_i :=  const_prop_i with_globals without_globals cpf in
  match ir with

  | Cassgn x tag ty e =>
    let globs := with_globals gd tag in
    let e := const_prop_e globs m e in
    let (m,x) := const_prop_rv globs m x in
    let m := add_cpm m x tag e cpf ty in
    (m, [:: MkI ii (Cassgn x tag ty e)])

  | Copn xs t o es =>
    (* TODO: Improve this *)
    let es := map (const_prop_e without_globals m) es in
    let (m,xs) := const_prop_rvs without_globals m xs in
    let ir :=
      if is_update_imm xs o es is Some (x, b, e) then
        if b then Copn [:: x ] AT_none (Oslh SLHmove) [:: e ]
        else Cassgn x AT_none ty_msf (wconst (sz := msf_size) (-1))
      else (Copn xs t o es)
    in
    (m, [:: MkI ii ir ])

  | Csyscall xs o es =>
    let es := map (const_prop_e without_globals m) es in
    let (m,xs) := const_prop_rvs without_globals m xs in
    (m, [:: MkI ii (Csyscall xs o es) ])

  | Cassert t p b =>
    let b := const_prop_e without_globals m b in
    let m := match b with
      | Pvar x => Mvar.set m x.(gv) (Cbool true)
      | Papp2 (Oeq ty) (Pvar x) (Pconst c) 
      | Papp2 (Oeq ty) (Pconst c) (Pvar x) => 
        Mvar.set m x.(gv) (Cint c)
      | _ => m 
    end in
    match is_bool b with
      | Some b =>
        let c := if b then [::] else [:: MkI ii (Cassert t p b)] in
        (m, c)
      | None => (m, [:: MkI ii (Cassert t p b) ])
    end

  | Cif b c1 c2 =>
    let b := const_prop_e without_globals m b in
    match is_bool b with
    | Some b =>
      let c := if b then c1 else c2 in
      const_prop const_prop_i m c
    | None =>
      let (m1,c1) := const_prop const_prop_i m c1 in
      let (m2,c2) := const_prop const_prop_i m c2 in
      (merge_cpm m1 m2, [:: MkI ii (Cif b c1 c2) ])
    end

  | Cfor x (dir, e1, e2) c =>
    let e1 := const_prop_e without_globals m e1 in
    let e2 := const_prop_e without_globals m e2 in
    let m := remove_cpm m (write_i ir) in
    let (_,c) := const_prop const_prop_i m c in
    (m, [:: MkI ii (Cfor x (dir, e1, e2) c) ])

  | Cwhile a c e info c' =>
    let wloop_fallback :=
      let m := remove_cpm m (write_i ir) in
      let (m',c) := const_prop const_prop_i m c in
      let (_,c') := const_prop const_prop_i m' c' in
      (m',(c,c'))
    in
    let dobody m' :=
      let (m1,c1) := const_prop const_prop_i m' c in
      let (m2,c2) := const_prop const_prop_i m1 c' in
      (m2,(m1,(c1,c2)))
    in
    let (m,cs) := wloop dobody wloop_fallback Loop.nb m in
    let e := const_prop_e without_globals m e in
    let cw :=
        match is_bool e with
        | Some false => cs.1
        | _          => 
          [:: MkI ii (Cwhile a cs.1 e info cs.2)]
        end
      in
    (m, cw)

  | Ccall xs f es =>
    let es := map (const_prop_e without_globals m) es in
    let (m,xs) := const_prop_rvs without_globals m xs in
    (m, [:: MkI ii (Ccall xs f es) ])

  end

with const_prop_i with_globals without_globals cpf (m:cpm) (i:instr) : cpm * cmd :=
  let (ii,ir) := i in
  const_prop_ir with_globals without_globals cpf m ii ir.

End GLOBALS.

Section Section.

Context {pT: progT}.

Let with_globals_cl (gd: glob_decls) : globals := Some (assoc gd).

Definition const_prop_ci without_globals ci :=
  let ci_pre := map (fun c =>
                        let truc := const_prop_e without_globals empty_cpm (snd c) in
                        (fst c, truc)) ci.(f_pre)
  in
  let ci_post := map (fun c =>
                        let truc := const_prop_e without_globals empty_cpm (snd c) in
                        (fst c, truc)) ci.(f_post)
  in
  MkContra ci.(f_iparams) ci.(f_ires) ci_pre ci_post.

Definition const_prop_fun (cl: bool) (gd: glob_decls) cpf (f: fundef) :=
  let with_globals := if cl then (fun _ _ => with_globals_cl gd) else with_globals in
  let without_globals := if cl then with_globals_cl gd else without_globals in
  let 'MkFun ii ci si p c so r ev := f in
  let mc := const_prop (const_prop_i gd with_globals without_globals cpf) empty_cpm c in
  let ci := Option.map (const_prop_ci without_globals) ci in
  MkFun ii ci si p mc.2 so r ev.
  
(* cpf is a function that indicates what should be propagated,
receiving the paraments of the Cassgn (with the exception of the type)
and returning a bool that indicates whether to propagate or not*)
Definition const_prop_prog_fun (cl:bool) (p:prog) (cpf:lval -> assgn_tag -> pexpr -> bool) : prog :=
  map_prog (const_prop_fun cl p.(p_globs) cpf) p.
 

Definition const_prop_prog (cl: bool) (p:prog) : prog :=
  const_prop_prog_fun cl p (fun _ tag _ =>  (tag == AT_inline)).

End Section.

End ASM_OP.
End WITH_PARAMS.
