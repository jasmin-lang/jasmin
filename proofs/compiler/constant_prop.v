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
  | Cword sz `(word sz)
  | Cfull_init of positive.

Definition const_v_beq (c1 c2: const_v) : bool :=
  match c1, c2 with
  | Cbool b1, Cbool b2 => b1 == b2
  | Cint z1, Cint z2 => z1 == z2
  | Cword sz1 w1, Cword sz2 w2 =>
    match wsize_eq_dec sz1 sz2 with
    | left e => eq_rect _ word w1 _ e == w2
    | _ => false
    end
  | Cfull_init p1 , Cfull_init p2 => p1 == p2
  | _, _ => false
  end.

Lemma const_v_eq_axiom : Equality.axiom const_v_beq.
Proof.
case => [ b1 | z1 | sz1 w1 | p1 ] [ b2 | z2 | sz2 w2 | p2 ] /=; try (constructor; congruence).
1-2,4: by case: eqP => [ -> | ne ]; constructor; congruence.
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
  | Cfull_init l => Pbarr_init (Pconst 1) l
  end.

Definition globals : Type := option (var → option glob_value).

Let without_globals : globals := None.
Let with_globals (gd: glob_decls) (tag: assgn_tag) : globals :=
  if tag is AT_inline then Some (assoc gd) else None.


Section CL_FLAG.

Context (cl : bool).

Definition empty_cpm : cpm := @Mvar.empty const_v.

Definition merge_cpm : cpm -> cpm -> cpm :=
  Mvar.map2 (fun _ (o1 o2: option const_v) =>
   match o1, o2 with
   | Some n1, Some n2 =>
     if (n1 == n2)%Z then Some n1
     else None
   | _, _ => None
   end).

Definition and_cpm : cpm -> cpm -> cpm :=
  Mvar.map2 (fun _ (o1 o2: option const_v) =>
   match o1, o2 with
   | Some n1, Some n2 =>
     if (n1 == n2)%Z then Some n1
     else None
   | Some n1, None => Some n1
   | None, Some n2 => Some n2
   | None, None => None
   end).

Definition includes_cpm (m1:cpm) (m2:cpm): bool :=
  Mvar.fold (fun x n1 b =>
    match Mvar.get m2 x with
    | Some n2 => (n1 == n2)%Z && b
    | None => true
    end) m1 true.



Definition remove_cpm (m:cpm) (s:Sv.t): cpm :=
  Sv.fold (fun x m => Mvar.remove m x) s m.

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
     match is_const s, is_const len, cl with
     | Some s, Some len, true=>
       foldl (fun acc i =>
               let m := Mvar.set m x (Cint i) in
               let b := const_prop_e m body in
               Papp2 op acc b)
             idx (ziota s len)
     | _, _ , _ =>
         Pbig idx op x (const_prop_e (Mvar.remove m x) body) s len
     end

   | Pis_var_init _ => e

   | Pis_barr_init x e1 e2 =>
     let e1 := const_prop_e m e1 in
     let e2 := const_prop_e m e2 in
     Pis_barr_init x e1 e2

   | Pis_arr_init x e1 e2 =>
     let e1 := const_prop_e m e1 in
     let e2 := const_prop_e m e2 in
     Pis_arr_init x e1 e2

   | Pis_mem_init e1 e2 =>
     let e1 := const_prop_e m e1 in
     let e2 := const_prop_e m e2 in
     Pis_mem_init e1 e2
   
   | Pbarr_init e l => 
     let e := const_prop_e m e in
     Pbarr_init e l
  
  end.

Definition op1_merge_m (m:cpm) (m':cpm) o :=
  if o == Onot then m else m'.

Definition wsize_of_stype (ty: stype) : wsize :=
  if ty is sword sz then sz else U64.


Definition op2_add_cpm (m:cpm) (e1:pexpr) (e2:pexpr) ty :=
if e1 is Pvar x then
    let x := x.(gv) in
    match e2, ty with
    | (Pbool b), _  => Mvar.set m x (Cbool b)
    | (Pconst z), _ =>  Mvar.set m x (Cint z)
    | (Papp1 (Oword_of_int _) (Pconst z)),(Op_w szty)  =>
      let szx := wsize_of_stype (vtype x) in
      let sz := cmp_min szty szx in
      let w := Cword (wrepr sz z) in
      Mvar.set m x w
    | _,_ => m
    end
else m.

Definition op2_merge_m (m:cpm) (m1:cpm) (m2:cpm) o  (e1:pexpr) (e2:pexpr):=
  match o with
  | Oand => and_cpm m1 m2 
  | Oor  => merge_cpm m1 m2
  | Oeq ty => and_cpm (op2_add_cpm m e1 e2 ty) (op2_add_cpm m e2 e1 ty)
  | _ => m      
  end.


Fixpoint const_prop_e_assert m e : cpm * pexpr := 
  match e with
  | Pvar x => 
    let e := const_prop_e m e in
    let m := match e with
     | Pvar {|gv:={|v_var:={|vtype:=sbool|}|}|} => Mvar.set m x.(gv) (Cbool true)
     | _ => m
     end in
    (m,e)
  | Papp1 o e     =>
    let (m',e) := const_prop_e_assert m e in
    let m := op1_merge_m m m' o in
    (m, s_op1 o e)
  | Papp2 o e1 e2 => 
    let (m1,e1) := const_prop_e_assert m e1 in
    let (m2,e2) := const_prop_e_assert m e2 in
    let m := op2_merge_m m m1 m2 o e1 e2 in
    (m, s_op2 o e1 e2)
  | Pif t e e1 e2 =>
    let e := const_prop_e m e in
    let (m1,e1) := const_prop_e_assert m e1 in
    let (m2,e2) := const_prop_e_assert m e2 in
    match is_bool e with
    | Some b =>
      let m := if b then m1 else m2 in
      (m, s_if t e e1 e2)
    | None =>
      let m := merge_cpm m1 m2 in
      (m, s_if t e e1 e2)
    end
  | Pis_barr_init x e1 e2 => 
    if Mvar.get m x is Some (Cfull_init _) then (m,Pbool true)
    else
     let e1 := const_prop_e m e1 in
     let e2 := const_prop_e m e2 in
     let m := match is_const e1, is_const e2, x.(v_var).(vtype) with
        | Some 0, Some e2, (sarr sz) => 
          if (Zpos sz) == e2 then
            Mvar.set m x (Cfull_init sz)
          else
            m
        | _,_,_ => m
     end
     in
     (m,Pis_barr_init x e1 e2) 
  | _ =>
      let e := const_prop_e m e in
      (m,e)
end.


End GLOBALS.

Definition empty_const_prop_e := const_prop_e without_globals empty_cpm.


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


Section LOOP.
  Context `{asmop : asmOp}.

  Variable cp_c : cpm ->  cpm * cmd.
  Variable cp_c2 : cpm ->  cpm * (cpm * (cmd*cmd)).

  Variable loop_fallback: cpm * cmd.

  Variable wloop_fallback: cpm * (cmd * cmd).

  Fixpoint loop (n:nat) (m:cpm) :=
    match n with
    | O => loop_fallback
    | S n =>
      let: (m', c'):= cp_c m in
      if includes_cpm m' m then (m,c')
      else loop n (merge_cpm m' m)
    end.
  
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
    | Pbarr_init (Pconst 1) l =>
        Mvar.set m x (Cfull_init l)
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

Fixpoint translate_vars_contract (p:seq var_i) (p':seq var_i) (m:cpm) : cpm :=
  match p, p' with
  | x::p, x'::p' =>
    if Mvar.get m x is Some n then
      translate_vars_contract p p' (Mvar.set m x' n)
    else
      translate_vars_contract p p' m
  | _ , _ => m
end.

Fixpoint const_prop_ir with_globals without_globals cpf  (m:cpm) ii (ir:instr_r) : cpm * cmd :=
  let const_prop_i :=  const_prop_i with_globals without_globals cpf  in
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
    let (m,b) := const_prop_e_assert without_globals m b in
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
    let loop_fallback := 
      let m := remove_cpm m (write_i ir) in
      let (_,c) := const_prop const_prop_i m c in
      (m,c)
    in
    let dobody m' :=
      let (m1,c1) := const_prop const_prop_i m' c in
      (m1,c1)
    in
    let (m,c) := loop dobody loop_fallback Loop.nb m in
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

with const_prop_i with_globals without_globals cpf  (m:cpm) (i:instr) : cpm * cmd :=
  let (ii,ir) := i in
  const_prop_ir with_globals without_globals cpf  m ii ir.

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


Definition const_prop_pre without_globals (f:fundef) (ci:fun_contract) :=
  let (m,ci_pre) := foldl (fun (m: cpm * seq (assertion_prover * pexpr)) (e:assertion_prover * pexpr)  =>
    let (m,es) := m in
    let (ap,e) := e in
    let (m,e) := const_prop_e_assert without_globals m e in
    (m,es ++ [::(ap,e)])
  ) (empty_cpm,[::])  ci.(f_pre) in
  let m := translate_vars_contract ci.(f_iparams) f.(f_params) m in
  let ci := MkContra ci.(f_iparams) ci.(f_ires) ci_pre ci.(f_post) in
  (m,Some ci).

Definition const_prop_post without_globals (m:cpm) (f:fundef) (ci:fun_contract) :=
  (*translate both the params and return vars to the contract variables*)
  let m := translate_vars_contract f.(f_params) ci.(f_iparams) m in
  let m := translate_vars_contract f.(f_res) ci.(f_ires) m in
  let (extra_body,ci_post) := foldl (fun (acc: cmd * seq (assertion_prover * pexpr)) (e:assertion_prover * pexpr)  =>
    let (extra_body,es) := acc in
    let (ap,e) := e in
    let (_,e) := const_prop_e_assert without_globals m e in
    (extra_body,es ++ [::(ap,e)])
  ) ([::],[::])  ci.(f_post) in
  let ci := MkContra ci.(f_iparams) ci.(f_ires) ci.(f_pre) ci_post in
  (extra_body,Some ci ).

Definition const_prop_fun (gd: glob_decls) cpf  (f: fundef) :=
  let with_globals := if cl then (fun _ _ => with_globals_cl gd) else with_globals in
  let without_globals := if cl then with_globals_cl gd else without_globals in
  let 'MkFun ii ci si p c so r ev := f in
  let ci := Option.map (const_prop_pre without_globals f) ci in
  let (m,ci) := if ci is Some ci then ci else (empty_cpm, None) in
  let mc := const_prop (const_prop_i gd with_globals without_globals cpf ) m c in
  (*FIXME - receives the current state but does not replace, only adds intructions to the body*)
  let ci := Option.map (const_prop_post without_globals empty_cpm f) ci in
  let (extra_body,ci) := if ci is Some ci then ci else ([::],None) in
  let c:= c ++ extra_body in
  MkFun ii ci si p mc.2 so r ev.
  
(* cpf is a function that indicates what should be propagated,
receiving the paraments of the Cassgn (with the exception of the type)
and returning a bool that indicates whether to propagate or not*)
Definition const_prop_prog_fun (p:prog) (cpf:lval -> assgn_tag -> pexpr -> bool) : prog :=
  map_prog (const_prop_fun p.(p_globs) cpf ) p.


Definition const_prop_prog (p:prog) : prog :=
  const_prop_prog_fun p (fun _ tag _ =>  (tag == AT_inline)).

End Section.

End ASM_OP.
End CL_FLAG.
End WITH_PARAMS.
