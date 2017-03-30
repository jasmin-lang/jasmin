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

(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr memory dmasm_sem.

Require Import compiler_util.
Require Import ZArith.
Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Module S.

  Record sfundef := MkSFun {
    sf_iinfo  : instr_info;
    sf_stk_sz : Z;
    sf_stk_id : Ident.ident; 
    sf_params : seq var_i;
    sf_body   : cmd;
    sf_res    : seq var_i;
  }.

  Definition sprog := seq (funname * sfundef).

  Notation vstk nstk := {|v_var := {|vtype := sword; vname := nstk|}; v_info := xH|}.

  Definition dummy_sfundef := 
    {| sf_iinfo := dummy_iinfo; 
       sf_stk_sz := 0;
       sf_stk_id := ""%string;
       sf_params := [::]; 
       sf_body := [::]; 
       sf_res := [::] |}.

  Section SEM.

  Variable P:sprog.

  Definition get_fundef f := 
    let pos := find (fun ffd => f == fst ffd) P in
    if pos <= size P then
      Some (snd (nth (xH,dummy_sfundef) P pos))
    else None.

  Import Memory.

  Inductive sem : estate -> cmd -> estate -> Prop :=
  | Eskip s : sem s [::] s

  | Eseq s1 s2 s3 i c :
    sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

  with sem_I : estate -> instr -> estate -> Prop :=
  | EmkI ii i s1 s2: 
    sem_i s1 i s2 ->
    sem_I s1 (MkI ii i) s2

  with sem_i : estate -> instr_r -> estate -> Prop :=
  | Eassgn s1 s2 (x:rval) tag e:
    (Let v := sem_pexpr s1 e in write_rval x v s1) = ok s2 ->
    sem_i s1 (Cassgn x tag e) s2

  | Eopn s1 s2 o xs es:
    sem_pexprs s1 es >>= sem_sopn o >>= (write_rvals s1 xs) = ok s2 ->
    sem_i s1 (Copn xs o es) s2

  | Eif_true s1 s2 e c1 c2 :
    sem_pexpr s1 e >>= to_bool = ok true ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

  | Eif_false s1 s2 e c1 c2 :
    sem_pexpr s1 e >>= to_bool = ok false ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

  | Ewhile_true s1 s2 s3 e c :
    sem_pexpr s1 e >>= to_bool = ok true ->
    sem s1 c s2 ->
    sem_i s2 (Cwhile e c) s3 ->
    sem_i s1 (Cwhile e c) s3

  | Ewhile_false s e c :
    sem_pexpr s e >>= to_bool = ok false ->
    sem_i s (Cwhile e c) s

  | Ecall s1 m2 s2 ii xs f args vargs vs :
    sem_pexprs s1 args = ok vargs ->
    sem_call s1.(emem) f vargs m2 vs ->
    write_rvals {|emem:= m2; evm := s1.(evm) |} xs vs = ok s2 ->
    sem_i s1 (Ccall ii xs f args) s2

  with sem_call : mem -> funname -> seq value -> mem -> seq value -> Prop :=
  | EcallRun m1 m2 fn sf vargs s1 s2 m2' vm2 vres p:
    get_fundef fn = Some sf ->
    alloc_stack m1 (sf_stk_sz sf) = ok p ->
    write_var  (vstk (sf_stk_id sf)) p.1 (Estate p.2 vmap0) = ok s1 ->
    write_vars (sf_params sf) vargs s1 = ok s2 ->
    sem s2 (sf_body sf) {| emem := m2'; evm := vm2 |} ->
    mapM (fun (x:var_i) => get_var vm2 x) sf.(sf_res) = ok vres ->
    m2 = free_stack m2' p.1 (sf_stk_sz sf) ->
    sem_call m1 fn vargs m2 vres.

  End SEM.

End S.


Definition map := (Mvar.t Z * Ident.ident)%type.

Definition size_of (t:stype) := 
  match t with
  | sword  => ok 1%Z
  | sarr n => ok (Zpos n)
  | _      => cerror (Cerr_stk_alloc "size_of")
  end.

Lemma size_of_pos t s : size_of t = ok s -> (1 <= s)%Z.
Proof. case: t=> //= [p [] <-|[] <-] //=; zify; omega. Qed.

Definition init_map (sz:Z) (nstk:Ident.ident) (l:list (var * Z)):=
  let add (vp:var*Z) (mp:Mvar.t Z * Z) :=
    if (mp.2 <=? vp.2)%Z then 
      Let s := size_of (vtype vp.1) in
      cok (Mvar.set mp.1 vp.1 vp.2, vp.2 + s)%Z
    else cerror (Cerr_stk_alloc "overlap") in
  Let mp := foldM add (Mvar.empty Z, 0%Z) l in 
  if (mp.2 <=? sz)%Z then cok (mp.1, nstk)
  else cerror (Cerr_stk_alloc "stack size").

Definition is_in_stk (m:map) (x:var) :=
  match Mvar.get m.1 x with 
  | Some _ => true
  | None   => false
  end.

Definition vstk (m:map) :=  {|vtype := sword; vname := m.2|}.
Definition estk (m:map) := Pvar {|v_var := vstk m; v_info := xH|}.

Definition is_vstk (m:map) (x:var) :=
  x == (vstk m).

Definition check_var (m:map) (x1 x2:var_i) :=
  ~~ is_in_stk m x1 && (v_var x1 == v_var x2) && ~~is_vstk m x1.

Definition check_var_stk (m:map) (x1 x2:var_i) (e2:pexpr) := 
  is_vstk m x2 && (vtype x1 == sword) &&
    match Mvar.get m.1 x1 with
    | Some ofs => e2 == (Pcast (Pconst ofs))
    | _ => false
    end.

Definition is_arr_type (t:stype) := 
  match t with
  | sarr _ => true
  | _      => false
  end.

Definition check_arr_stk' check_e (m:map) (x1:var_i) (e1:pexpr) (x2:var_i) (e2:pexpr) :=
  is_vstk m x2 && is_arr_type (vtype x1) &&
    match Mvar.get m.1 x1 with
    | Some ofs =>
      match e2 with
      | Pcast (Papp2 Oadd (Pconst ofs') e2') => (ofs == ofs') && check_e m e1 e2'
      | _ => false
      end ||
      match e2 with
      | Pcast (Papp2 Oadd e2' (Pconst ofs')) => (ofs == ofs') && check_e m e1 e2'
      | _ => false
      end ||
      match e1 with
      | Pconst n => e2 == Pcast (Pconst (ofs + n)) 
      | _        => false
      end
    | _ => false
    end.

Fixpoint check_e (m:map) (e1 e2: pexpr) :=
  match e1, e2 with 
  | Pconst n1, Pconst n2 => n1 == n2 
  | Pbool  b1, Pbool  b2 => b1 == b2 
  | Pcast  e1, Pcast  e2 => check_e m e1 e2 
  | Pvar   x1, Pvar   x2 => check_var m x1 x2 
  | Pvar   x1, Pload x2 e2 => check_var_stk m x1 x2 e2
  | Pget  x1 e1, Pget x2 e2 => check_var m x1 x2 && check_e m e1 e2
  | Pget  x1 e1, Pload x2 e2 => check_arr_stk' check_e m x1 e1 x2 e2
  | Pload x1 e1, Pload x2 e2 => check_var m x1 x2 && check_e m e1 e2
  | Pnot   e1, Pnot   e2 => check_e m e1 e2 
  | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
    (o1 == o2) && check_e m e11 e21 && check_e m e12 e22
  | _, _ => false
  end.

Definition check_arr_stk := check_arr_stk' check_e.

Definition check_rval (m:map) (r1 r2:rval) := 
  match r1, r2 with
  | Rnone _, Rnone _ => true
  | Rvar x1, Rvar x2 => check_var m x1 x2
  | Rvar x1, Rmem x2 e2 => check_var_stk m x1 x2 e2
  | Rmem x1 e1, Rmem x2 e2 => check_var m x1 x2 && check_e m e1 e2
  | Raset x1 e1, Raset x2 e2 => check_var m x1 x2 && check_e m e1 e2
  | Raset x1 e1, Rmem x2 e2 => check_arr_stk m x1 e1 x2 e2
  | _, _ => false
  end.

Fixpoint check_i (m: map) (i1 i2: instr) : bool :=
  let (_, ir1) := i1 in
  let (_, ir2) := i2 in
  match ir1, ir2 with
  | Cassgn r1 _ e1, Cassgn r2 _ e2 => check_rval m r1 r2 && check_e m e1 e2
  | Copn rs1 o1 e1, Copn rs2 o2 e2 => all2 (check_rval m) rs1 rs2 && (o1 == o2) && all2 (check_e m) e1 e2
  | Cif e1 c1 c1', Cif e2 c2 c2' => check_e m e1 e2 && all2 (check_i m) c1 c2 && all2 (check_i m) c1' c2'
  | Cwhile e1 c1, Cwhile e2 c2 => check_e m e1 e2 && all2 (check_i m) c1 c2
  | _, _ => false
  end.

(* --------------------------------------------------------------------------- *)

Local Open Scope Z_scope.

Definition stk_ok (w:word) (z:Z) := w + z < I64.modulus.

Definition valid_map (m:map) (stk_size:Z) := 
  forall x px, Mvar.get m.1 x = Some px -> 
     exists sx, size_of (vtype x) = ok sx /\
     [/\ 0 <= px, px + sx <= stk_size &
         forall y py sy, x != y ->  
           Mvar.get m.1 y = Some py -> size_of (vtype y) = ok sy ->
           px + sx <= py \/ py + sy <= px].

Section PROOF.
  Variable P: prog.
  Variable SP: S.sprog.

  Variable m:map.
  Variable stk_size : Z.
  Variable pstk : word.

  Hypothesis pstk_add : stk_ok pstk stk_size.

  Hypothesis validm : valid_map m stk_size.

  Import Memory.

  Definition valid_stk (vm1:vmap) (m2:mem) pstk :=
    forall x,
      match Mvar.get m.1 x with
      | Some p =>
        match vtype x with
        | sword =>
          valid_addr m2 (I64.repr (pstk + p)) /\
          let sv := vm1.[{|vtype:=sword;vname := vname x|}] in
          forall v, sv = ok v ->
            read_mem m2 (I64.repr (pstk + p)) = ok v
        | sarr s =>
          forall off, (0 <= off < Zpos s)%Z ->
            valid_addr m2 (I64.repr (pstk + (off + p))) /\
            let t := vm1.[{|vtype := sarr s;vname := vname x|}] in
            forall a, t = ok a ->
              forall v, FArray.get a off = ok v ->
                read_mem m2 (I64.repr (pstk + (off + p))) = ok v
        | _ => True
        end
      | _ => True
      end.

  Definition eq_vm (vm1 vm2:vmap) := 
    (forall (x:var), ~~ is_in_stk m x -> ~~ is_vstk m x -> vm1.[x] = vm2.[x]).

  Lemma eq_vm_write vm1 vm2 x v:
    eq_vm vm1 vm2 ->
    eq_vm vm1.[x <- v] vm2.[x <- v].
  Proof.
    move=> Heqvm w ??.
    case Heq: (w == x).
    + move: Heq=> /eqP ->; by rewrite !Fv.setP_eq.
    + move: Heq=> /negPf Heq.
      by rewrite !Fv.setP_neq ?Heqvm // eq_sym Heq.
  Qed.

  Definition disjoint_stk m := 
    forall w, valid_addr m w -> ~(pstk <= w < pstk + stk_size).

  Definition valid (s1 s2:estate) :=
    [/\ disjoint_stk (emem s1), 
        (forall w, valid_addr (emem s1) w -> read_mem (emem s1) w = read_mem (emem s2) w),
        (forall w, valid_addr (emem s2) w = valid_addr (emem s1) w ||  
                                       ((pstk <=? w) && (w <? pstk + stk_size))),
        eq_vm (evm s1) (evm s2) & 
        get_var (evm s2) (vstk m) = ok (Vword pstk) /\
        valid_stk (evm s1) (emem s2) pstk ].

  Lemma get_valid_wrepr x p: 
     Mvar.get m.1 {| vtype := sword; vname := x |} = Some p -> 
     pstk + p = I64.repr (pstk + p).
  Proof.
    move=> Hget; have [sx /= [][]<-[]?? _]:= validm Hget.
    rewrite I64.unsigned_repr //.
    move: pstk_add (I64.unsigned_range pstk);rewrite /stk_ok/I64.max_unsigned.
    move=> ??;omega.
  Qed.

  Lemma get_valid_arepr x n p p1 : 
    Mvar.get m.1 {| vtype := sarr n; vname := x |} = Some p ->
    0 <= p1 < Z.pos n ->
    pstk + (p1 + p) = I64.repr (pstk + (p1 + p)).
  Proof.
    move=> Hget Hp1; have [sx /= [][]<-[]?? _]:= validm Hget.
    rewrite I64.unsigned_repr //.
    move: pstk_add (I64.unsigned_range pstk);rewrite /stk_ok/I64.max_unsigned.
    move=> ??;omega.
  Qed.

  Lemma get_valid_repr x sz get:
    size_of (vtype x) = ok sz ->
    Mvar.get m.1 x = Some get ->
    pstk + get = I64.repr (pstk + get).
  Proof.
    move=> Hsz Hget.
    case: x Hget Hsz=> [[]] //.
    + move=> n vn Hget _.
      have ->: get = 0 + get by [].
      by rewrite {1}(get_valid_arepr Hget).
    + move=> vn Hget _.
      by rewrite {1}(get_valid_wrepr Hget).
  Qed.

  Lemma get_valid_word x p m1 m2: 
     valid m1 m2 -> 
     Mvar.get m.1 {| vtype := sword; vname := x |} = Some p -> 
     valid_addr (emem m2) (I64.repr (pstk + p)).
  Proof.
    move=> [] H0 H1 _ H2 [H3 H4] Hget.
    by have := H4 {| vtype := sword; vname := x |};rewrite Hget /= => -[-> _].
  Qed.

  Lemma get_valid_arr x n p p1 m1 m2: 
     valid m1 m2 -> 
     Mvar.get m.1 {| vtype := sarr n; vname := x |} = Some p -> 
     0 <= p1 < Zpos n ->
     valid_addr (emem m2) (I64.repr (pstk + (p1 + p))).
  Proof.
    move=> [] H0 H1 _ H2 [H3 H4] Hget Hp1.
    by have := H4 {| vtype := sarr n; vname := x |};rewrite Hget /= => /(_ _ Hp1) [].
  Qed.

  Lemma read_write_mem m1 v1 v2 m2 w:
    write_mem m1 v1 v2 = ok m2 ->
    read_mem m2 w = write_mem m1 v1 v2 >>= (fun m2 => read_mem m2 w).
  Proof. by move=> ->. Qed.

  Lemma write_valid m1 m2 v1 v2 w:
    write_mem m1 v1 v2 = ok m2 ->
    valid_addr m1 w = valid_addr m2 w.
  Proof.
    move=> H1.
    have Hr := read_write_mem _ H1.
    have Hv1 : valid_addr m1 v1 by apply /(writeV m1 v1 v2);exists m2.
    case Hw: (valid_addr m1 w);move /readV: (Hw).
    + move=> [w' Hw'];symmetry.
      case (v1 =P w) => [ | /eqP] Heq.
      + by subst;apply /readV;exists v2; rewrite Hr Memory.writeP Hv1 eq_refl.
      by apply /readV;exists w'; rewrite Hr Memory.writeP (negbTE Heq) Hv1.
    move=> Hm1;symmetry;apply /readV => -[w'].
    rewrite Hr Memory.writeP Hv1;case:ifP => /eqP Heq.
    + by subst;move: Hv1;rewrite Hw.
    by move=> ?;apply Hm1;exists w'.
  Qed.

  Lemma read_mem_write_same addr addr' val m1 m2 m1' m2':
    write_mem m1 addr val = ok m1' ->
    write_mem m2 addr val = ok m2' ->
    (forall w, valid_addr m1 w -> read_mem m1 w = read_mem m2 w) ->
    valid_addr m1 addr' ->
    read_mem m1' addr' = read_mem m2' addr'.
  Proof.
    move=> Hw1 Hw2 Hother Hv'.
    have Hv1: valid_addr m1 addr.
      apply/writeV; exists m1'; exact: Hw1.
    have Hv2: valid_addr m2 addr.
      apply/writeV; exists m2'; exact: Hw2.
    rewrite (read_write_mem _ Hw1) (read_write_mem _ Hw2) !writeP Hv1 Hv2 Hother //.
  Qed.

  Lemma add_repr_r x y : I64.add x (I64.repr y) = I64.repr (x + y).
  Proof.
    by apply: reqP; rewrite !urepr !I64.Z_mod_modulus_eq Zplus_mod_idemp_r eq_refl.
  Qed.

  Lemma check_varP vm1 vm2 x1 x2:
    check_var m x1 x2 -> eq_vm vm1 vm2 -> get_var vm1 x1 = get_var vm2 x2.
  Proof.
    move=> /andP [/andP [Hin_stk /eqP Heq12] Hnot_vstk] Heq.
    rewrite /get_var Heq12 Heq=> //; by rewrite -Heq12.
  Qed.

  Lemma check_var_stkP s1 s2 x1 x2 e v:
    check_var_stk m x1 x2 e ->
    valid s1 s2 ->
    sem_pexpr s1 (Pvar x1) = ok v ->
    sem_pexpr s2 (Pload x2 e) = ok v.
  Proof.
    move=> /andP [/andP [/eqP Hvstk /eqP Htype] Hget] Hvalid /=.
    case Hget: (Mvar.get m.1 x1) Hget=> [ofs|//] /eqP ->.
    rewrite /=.
    move: Hvalid=> -[] _ _ _ _ [Hpstk /(_ x1) H].
    rewrite Hget Htype in H.
    move: H=> [H H'] Hvar.
    rewrite Hvstk Hpstk /=.
    case: x1 Htype Hget Hvar H'=> [[x1t x1n] vi1] /= Htype Hget Hvar H'.
    rewrite Htype in Hget.
    rewrite add_repr_r.
    rewrite /= in H'.
    rewrite /get_var in Hvar.
    move: Hvar.
    apply: rbindP=> var Hvar []<-.
    move: var Hvar=> /=.
    rewrite Htype=> var Hvar.
    by rewrite (H' _ Hvar).
  Qed.

  Lemma check_arr_stkP s1 s2 x1 e1 x2 e2 v:
    check_arr_stk m x1 e1 x2 e2 ->
    (forall e2' v, check_e m e1 e2' -> sem_pexpr s1 e1 = ok v -> sem_pexpr s2 e2' = ok v) ->
    valid s1 s2 ->
    sem_pexpr s1 (Pget x1 e1) = ok v ->
    sem_pexpr s2 (Pload x2 e2) = ok v.
  Proof.
    move=> /andP [/andP [Hvstk Harrt] Hget] Hcheck Hvalid.
    case Hget: (Mvar.get m.1 x1) Hget=> [ofs|//] Het.
    rewrite /=.
    apply: on_arr_varP=> n t Ht Harr.
    apply: rbindP=> i.
    apply: rbindP=> x Hx Hx'.
    apply: rbindP=> w Hw []<-.
    move: Hvalid=> -[] _ _ _ _ [Hpstk /(_ x1) H].
    rewrite Hget in H.
    move: Hvstk=> /eqP ->.
    rewrite Hpstk.
    case: x1 Harrt Hget Ht Harr H=> [[x1t x1n] vi1] /= Harrt Hget Ht Harr H.
    rewrite Ht in H.
    move: H=> /(_ i) [|].
    rewrite /Array.get in Hw.
    case Hbound: ((0 <=? i) && (i <? Z.pos n)) Hw =>// _.
    move: Hbound=> /andP [/Zle_bool_imp_le Hbound1 Hbound2].
    split=> //.
    by apply Z.ltb_lt.
    move=> Hvalid /(_ t _ w) H.
    have Hrmem: Let w0 := read_mem (emem s2) (I64.add pstk (I64.repr (ofs + i))) in ok (Vword w0) = ok (Vword w).
      rewrite add_repr_r.
      rewrite [ofs + i]Z.add_comm.
      rewrite H //.
      rewrite /get_var Ht in Harr.
      case: (bindW Harr)=> z ->.
      rewrite /to_val /=.
      move: z=> /= z Hok.
      have Hinj: forall x y, ok x = ok y -> x = y by move=> ???? [].
      congr (_ _).
      have Hinj': Varr z = Varr t by apply: Hinj; exact: Hok.
      by rewrite (proj2 (Varr_inj Hinj')).
      rewrite /Array.get in Hw.
      case: (_ && _) Hw=> //.
    move: Het=> /orP; case.
    move=> /orP; case.
    + case: e2=> // -[] // [] // [] // ofs' e2' /andP [/eqP <- He].
      rewrite /= (Hcheck _ _ He Hx) /=.
      by rewrite /sem_op2_i /mk_sem_sop2 /= Hx'.
    + case: e2=> // -[] // [] // e2' [] // ofs' /andP [/eqP <- He].
      rewrite /= (Hcheck _ _ He Hx) /=.
      rewrite /sem_op2_i /mk_sem_sop2 /= Hx' /=.
      rewrite [i + ofs]Z.add_comm //.
    + case: e1 Hx Hcheck=> // z Hx Hcheck /eqP -> /=.
      rewrite /= in Hx.
      move: Hx=> [].
      case: x Hx'=> //= z0 [] -> []-> //.
  Qed.

  Lemma check_eP (e1 e2: pexpr) (s1 s2: estate) v :
    check_e m e1 e2 -> valid s1 s2 -> sem_pexpr s1 e1 = ok v -> sem_pexpr s2 e2 = ok v.
  Proof.
    move=> He Hv; move: He.
    have Hvm: eq_vm (evm s1) (evm s2).
      by move: Hv=> -[].
    elim: e1 e2 v=> [c1|c1|e1 IH|v1|v1 e1 IH|v1 e1 IH|e1 IH|o1 e1 H1 e1' H1'] e2 v; try (by case: e2=> //= c2 /eqP ->).
    + case: e2=> //= e2 He.
      apply: rbindP=> z.
      apply: rbindP=> x Hx Hz []<-.
      by rewrite (IH _ _ He Hx) /= Hz.
    + case: e2=> // v2.
      move=> /check_varP H /= Hv1.
      by rewrite -(H _ _ Hvm).
    + move=> e /check_var_stkP Hvarstk.
      exact: Hvarstk.
    + case: e2=> // v2 e2.
      move=> /= /andP [Hv12 He12].
      apply: on_arr_varP=> n t Ht Harr.
      apply: rbindP=> i.
      apply: rbindP=> x Hx Hx'.
      apply: rbindP=> w Hw []<-.
      move: Hv12=> /check_varP.
      move=> /(_ _ _ Hvm) H.
      rewrite /on_arr_var -H.
      rewrite Harr /=.
      move: IH=> /(_ _ _ He12 Hx) -> /=.
      by rewrite Hx' /= Hw.
    + move=> He Hv1.
      apply: (check_arr_stkP He _ Hv Hv1).
      exact: IH.
    + case: e2=> // v2 e2 /= /andP [Hv12 He12].
      apply: rbindP=> w1.
      apply: rbindP=> x1 Hx1 Hw1.
      apply: rbindP=> w2.
      apply: rbindP=> x2 Hx2 Hw2.
      apply: rbindP=> w Hw -[] <-.
      rewrite -(check_varP Hv12 Hvm).
      rewrite Hx1 /= Hw1 /=.
      rewrite (IH _ _ He12 Hx2) /= Hw2 /=.
      have Hw': read_mem (emem s2) (I64.add w1 w2) = ok w.
        rewrite -Hw.
        move: Hv=> -[] _ -> //.
        apply/readV; exists w; exact: Hw.
      by rewrite Hw'.
    + case: e2=> // e2 /= He.
      apply: rbindP=> b.
      apply: rbindP=> x Hx Hb []<-.
      by rewrite (IH _ _ He Hx) /= Hb.
    + case: e2=> // o2 e2 e2' /= /andP [/andP [/eqP -> /H1 He] /H1' He'].
      apply: rbindP=> v1 Hv1.
      apply: rbindP=> v2 Hv2 <-.
      by rewrite (He _ Hv1) (He' _ Hv2).
  Qed.

  Lemma check_esP (es es': pexprs) (s1 s2: estate) vs :
    all2 (check_e m) es es' -> valid s1 s2 ->
    sem_pexprs s1 es = ok vs ->
    sem_pexprs s2 es' = ok vs.
  Proof.
    elim: es es' vs=> //= [|a l IH] [] // a' l' vs /andP [Ha Hl] Hvalid.
    rewrite /sem_pexprs /=.
    rewrite -![mapM _ _]/(sem_pexprs _ _).
    apply: rbindP=> y Hy.
    apply: rbindP=> ys Hys []<-.
    rewrite (IH _ _ Hl Hvalid Hys) /=.
    by rewrite (check_eP _ Hvalid Hy).
  Qed.

  Lemma valid_stk_write_notinstk s1 s2 vi v:
    ~~ (is_in_stk m vi) ->
    valid_stk (evm s1) (emem s2) pstk ->
    valid_stk (evm s1).[vi <- ok v] (emem s2) pstk.
  Proof.
    move=> Hnotinstk Hstk x.
    move: Hstk=> /(_ x).
    case Hget: (Mvar.get m.1 x)=> [get|] //.
    have Hx: x != vi.
      apply/negP=> /eqP Habs.
      by rewrite /is_in_stk -Habs Hget in Hnotinstk.
      case Htype: (vtype x)=> // [p|].
      + move=> H off Hoff.
        move: H=> /(_ off Hoff) [H H'].
        split=> //.
        move=> t a0 Ht v0 Haget.
        rewrite /= in H'.
        have Hvma: (evm s1).[{| vtype := sarr p; vname := vname x |}] = ok a0.
          rewrite -Ht /t Fv.setP_neq //.
          case: x Hget Hx Htype t a0 Ht Haget H'=> [xt xn] /= ?? Htype ?????.
          by rewrite -Htype eq_sym.
        by rewrite (H' _ Hvma _ Haget).
      + move=> [H H']; split=> // sv v0 Hv0.
        apply: H'.
        rewrite -Hv0 /sv Fv.setP_neq // /=.
        case: x Hget Hx Htype sv v0 Hv0=> [xt xn] /= Hget Hx Htype sv v0 Hv0.
        by rewrite -Htype eq_sym.
  Qed.

  Lemma check_varW (vi vi': var_i) (s1 s2: estate) v :
    check_var m vi vi' -> valid s1 s2 -> forall s1', write_var vi v s1 = ok s1' ->
    exists s2', write_var vi' v s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> /andP [/andP [Hnotinstk /eqP Heq] Hnotstk] Hv s1'.
    apply: rbindP=> z /=.
    apply: rbindP=> z0 Hz0 []<- []<-.
    exists {| emem := emem s2; evm := (evm s2).[vi <- ok z0] |}; split.
    by rewrite /write_var /set_var -Heq Hz0 /=.
    move: Hv=> [] H1 H2 H3 H4 [H5 H6].
    split=> //=.
    + exact: eq_vm_write.
    + split.
      case: (bindW H5)=> x Hx []<-.
      rewrite /get_var Fv.setP_neq ?Hx //.
      exact: valid_stk_write_notinstk.
  Qed.

  Lemma vtype_diff x x': vtype x != vtype x' -> x != x'.
  Proof.
    case: x=> vt vn /=.
    case: x'=> vt' vn' /= /negPf Hneq.
    apply/negP=> /eqP [] /eqP Habs _.
    by rewrite Habs in Hneq.
  Qed.

  Lemma vname_diff x x': vname x != vname x' -> x != x'.
  Proof.
    case: x=> vt vn /=.
    case: x'=> vt' vn' /= /negPf Hneq.
    apply/negP=> /eqP [] _ /eqP Habs.
    by rewrite Habs in Hneq.
  Qed.

  Lemma var_stk_diff x x' get get' sz:
    Mvar.get m.1 x = Some get ->
    Mvar.get m.1 x' = Some get' ->
    x != x' ->
    size_of (vtype x') = ok sz ->
    get != get'.
  Proof.
    move=> Hget Hget' Hneq Hsz.
    apply/negP=> /eqP Habs.
    rewrite -{}Habs in Hget'.
    move: (validm Hget)=> [sx [Hsx1 [Hsx2 Hsx3 /(_ _ _ _ Hneq Hget' Hsz) [|]]]].
    have := (size_of_pos Hsx1); lia.
    have := (size_of_pos Hsz); lia.
  Qed.

  Lemma var_stk_diff_off x x' get get' off sz:
    Mvar.get m.1 x = Some get ->
    Mvar.get m.1 x' = Some get' ->
    x != x' ->
    size_of (vtype x') = ok sz ->
    0 <= off < sz ->
    get != off + get'.
  Proof.
    move=> Hget Hget' Hneq Hsz Hoff.
    apply/negP=> /eqP Habs.
    rewrite {}Habs in Hget.
    move: (validm Hget)=> [sx [Hsx1 [Hsx2 Hsx3 /(_ _ _ _ Hneq Hget' Hsz) [|]]]].
    have := (size_of_pos Hsx1); lia.
    have := (size_of_pos Hsz); lia.
  Qed.

  Lemma var_stk_diff_off_l x x' get get' off sz:
    Mvar.get m.1 x = Some get ->
    Mvar.get m.1 x' = Some get' ->
    x != x' ->
    size_of (vtype x) = ok sz ->
    0 <= off < sz ->
    get + off != get'.
  Proof.
    move=> Hget Hget' Hneq Hsz Hoff.
    apply/negP=> /eqP Habs.
    rewrite -{}Habs in Hget'.
    rewrite eq_sym in Hneq.
    move: (validm Hget')=> [sx [Hsx1 [Hsx2 Hsx3 /(_ _ _ _ Hneq Hget Hsz) [|]]]].
    have := (size_of_pos Hsx1); lia.
    have := (size_of_pos Hsz); lia.
  Qed.

  Lemma valid_get_w vn get:
    Mvar.get m.1 {| vtype := sword; vname := vn |} = Some get ->
    (pstk <=? I64.add pstk (I64.repr get)) && (I64.add pstk (I64.repr get) <? pstk + stk_size).
  Proof.
    move=> Hget.
    move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' _]]].
    apply/andP; split.
    apply: Zle_imp_le_bool.
    rewrite add_repr_r.
    rewrite -(get_valid_wrepr Hget); lia.
    rewrite add_repr_r.
    apply Zlt_is_lt_bool.
    rewrite -(get_valid_wrepr Hget); lia.
  Qed.

  Lemma valid_get_a vn get n:
    Mvar.get m.1 {| vtype := sarr n; vname := vn |} = Some get ->
    (pstk <=? I64.add pstk (I64.repr get)) && (I64.add pstk (I64.repr get) <? pstk + stk_size).
  Proof.
    move=> Hget.
    move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' _]]].
    have ->: get = 0 + get by [].
    apply/andP; split.
    apply: Zle_imp_le_bool.
    rewrite add_repr_r.
    rewrite -(get_valid_arepr Hget); lia.
    rewrite add_repr_r.
    apply Zlt_is_lt_bool.
    rewrite -(get_valid_arepr Hget); lia.
  Qed.

  Lemma check_var_stkW (vi vi': var_i) (s1 s2: estate) v e:
    check_var_stk m vi vi' e -> valid s1 s2 -> forall s1', write_var vi v s1 = ok s1' ->
    exists s2' : estate, write_rval (Rmem vi' e) v s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> /andP [/andP [Hisvstk /eqP Htype] He] Hv.
    case Hget: (Mvar.get m.1 vi) He=> [get|//] /eqP -> s1'.
    case: vi Htype Hget=> [[vt vn] vi] /= Htype Hget.
    rewrite Htype.
    rewrite Htype in Hget.
    apply: rbindP=> /= z.
    apply: rbindP=> /= z0 Hz0 []<- []<-.
    rewrite Hz0 /=.
    move: Hv=> [] H1 H2 H3 H4 [H5 H6].
    move: Hisvstk=> /eqP ->.
    rewrite H5 /=.
    have Hvmem: valid_addr (emem s2) (I64.add pstk (I64.repr get)).
      rewrite H3.
      apply/orP; right; apply: (valid_get_w Hget).
    have Hmem: exists m', write_mem (emem s2) (I64.add pstk (I64.repr get)) z0 = ok m'.
      by apply/writeV.
    move: Hmem=> [m' Hm'].
    exists {| emem := m'; evm := evm s2 |}; split.
    by rewrite Hm' /=.
    split=> //=.
    + move=> w Hvalid.
      rewrite /disjoint_stk in H1.
      rewrite (read_write_mem w Hm').
      rewrite writeP Hvmem.
      rewrite (H2 _ Hvalid).
      suff ->: I64.add pstk (I64.repr get) == w = false=> //.
      rewrite add_repr_r.
      apply/negP=> /eqP Habs.
      have := (get_valid_wrepr Hget).
      rewrite Habs.
      have := (H1 _ Hvalid).
      move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' _]]].
      lia.
    + move=> w.
      by rewrite -(write_valid _ Hm') H3.
    + move=> x Hx1 Hx2.
      rewrite Fv.setP_neq.
      apply: H4=> //.
      apply/negP=> /eqP Habs.
      by rewrite -Habs /is_in_stk Hget in Hx1.
    + split=> // x.
      (* Prove valid_stk: long! *)
      move: H6=> /(_ x).
      case Hget': (Mvar.get m.1 x)=> [getx|//].
      case Htypex: (vtype x)=> [ | |n| ] //.
      + (* here, x <> vi *)
        move=> H off Hoff.
        move: H=> /(_ off Hoff) [Hoff1 Hoff2]; split.
        by rewrite -(write_valid _ Hm').
        rewrite Fv.setP_neq=> [t a Ht v0 Hv0|].
        rewrite (read_write_mem _ Hm') writeP Hvmem.
        rewrite (Hoff2 _ Ht _ Hv0).
        case: ifP=> // Heq; exfalso.
        rewrite add_repr_r in Heq.
        have Heq': get = (off + getx).
          apply (Z.add_cancel_l _ _ pstk).
          case: x Hget' Htypex Hoff2 t a Ht Hv0=> [xt xn] /= Hget' Htypex ?????.
          rewrite Htypex in Hget'.
          rewrite (get_valid_wrepr Hget) (get_valid_arepr Hget')=> //.
          by apply/eqP.
        have Habs: get != off + getx.
          apply: (var_stk_diff_off Hget Hget')=> //.
          rewrite vtype_diff //= Htypex //.
          rewrite Htypex /=; reflexivity.
          by [].
        by rewrite Heq' eq_refl in Habs.
        by rewrite vtype_diff.
      + move=> [H H']; split=> //.
        by rewrite -(write_valid _ Hm').
        case Heq: (vn == (vname x)).
        + move: Heq=> /eqP Heq.
          rewrite Heq.
          rewrite Fv.setP_eq /= => v0 [] <-.
          have ->: getx = get.
            have Hgeteq: Some getx = Some get.
              rewrite -Hget -Hget'.
              congr (_ _).
              case: x Hget' Htypex H' Heq=> xt xn ? Htypex ? ->.
              rewrite /= in Htypex.
              by rewrite /= -Htypex.
            by move: Hgeteq=> [].
          by rewrite (read_write_mem _ Hm') writeP Hvmem add_repr_r eq_refl.
        + rewrite Fv.setP_neq.
          rewrite /= => v0 Hv0.
          rewrite (read_write_mem _ Hm') writeP Hvmem add_repr_r.
          case: ifP=> // Heq'.
          + exfalso.
            have Heq'': get = getx.
              apply (Z.add_cancel_l _ _ pstk).
              case: x Hget' Htypex H' Heq Hv0=> xt xn /= Hget' Htypex ???.
              rewrite Htypex in Hget'.
              rewrite (get_valid_wrepr Hget) (get_valid_wrepr Hget').
              by apply/eqP.
            have Habs: get != getx.
              apply: (var_stk_diff Hget Hget')=> //.
              by rewrite vname_diff //= Heq.
              rewrite Htypex //=.
            move: Heq''=> /eqP Heq''.
            by rewrite Heq'' in Habs.
          + rewrite (H' _ Hv0) //.
            rewrite vname_diff=> //=.
            by rewrite Heq.
  Qed.

  (* TODO: move *)
  Lemma arr_set_ok n (a: Array.array n word) i v t:
    Array.set a i v = ok t ->
    0 <= i < Z.pos n.
  Proof.
    rewrite /Array.set.
    case Hind: ((0 <=? i) && (i <? Z.pos n))=> // _.
    move: Hind=> /andP [H1 H2].
    split; [by apply/Z.leb_le|by apply/Z.ltb_lt].
  Qed.

  Lemma check_arr_stkW (vi vi': var_i) (s1 s2: estate) v e e':
    check_arr_stk m vi e vi' e' -> valid s1 s2 -> forall s1', write_rval (Raset vi e) v s1 = ok s1' ->
    exists s2', write_rval (Rmem vi' e') v s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Harr Hv s1'.
    have := Hv => [[]] H1 H2 H3 H4 [H5 H6].
    apply: rbindP=> [[]] // n a Ha.
    (* TODO: this seems more complicated than it should.. *)
    have Hvi: v_var vi = {| vtype := sarr n; vname := vname vi |}.
      case: vi Harr Ha=> [[vt vn] vii] /= Harr Ha.
      rewrite /get_var in Ha.
      case: (bindW Ha)=> /= x Hx [].
      rewrite /to_val.
      case: vt x Hx Harr Ha=> // n' /= x Hx Harr Ha Hvara.
      by have := (Varr_inj Hvara)=> -[] -> _.
    apply: rbindP=> i.
    apply: rbindP=> vali Hvali Hi.
    apply: rbindP=> v0 Hv0.
    apply: rbindP=> t Ht.
    apply: rbindP=> vm.
    apply: rbindP=> varr Hvarr []<- []<-.
    rewrite /=.
    move: Harr=> /andP [/andP [Hisstk Harr] He'].
    move: Hisstk=> /eqP -> {vi'}.
    rewrite H5 /= Hv0 /=.
    case Hget: (Mvar.get m.1 vi) He'=> [get|//] He'.
    have Hall: exists s2' : estate,
      Let m0 := write_mem (emem s2) (I64.add pstk (I64.repr (get + i))) v0
      in ok {| emem := m0; evm := evm s2 |} = ok s2' /\
      valid {| emem := emem s1; evm := (evm s1).[vi <- ok varr] |} s2'.
      move: He'=> _.
      rewrite Hvi in Hget.
      have Hvmem: valid_addr (emem s2) (I64.add pstk (I64.repr (get + i))).
        rewrite add_repr_r [get + i]Z.add_comm.
        apply (get_valid_arr Hv Hget).
        exact: (arr_set_ok Ht).
      have Hmem: exists m', write_mem (emem s2) (I64.add pstk (I64.repr (get + i))) v0 = ok m'.
        by apply/writeV.
      move: Hmem=> [m' Hm'].
      rewrite Hm' /=.
      exists {| emem := m'; evm := evm s2 |}; split=> //=.
      split=> //=.
      + move=> w Hvmem'.
        rewrite /disjoint_stk in H1.
        rewrite (read_write_mem w Hm') writeP Hvmem.
        rewrite (H2 _ Hvmem').
        suff ->: I64.add pstk (I64.repr (get + i)) == w = false=> //.
        rewrite add_repr_r.
        apply/negP=> /eqP Habs.
        have Hi' := (arr_set_ok Ht).
        have := (get_valid_arepr Hget Hi').
        rewrite [get + i]Z.add_comm in Habs.
        rewrite Habs.
        have := (H1 _ Hvmem').
        move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' _]]].
        lia.
      + move=> w.
        by rewrite -(write_valid _ Hm') H3.
      + move=> x Hx1 Hx2.
        rewrite Fv.setP_neq.
        apply: H4=> //.
        apply/negP=> /eqP Habs.
        rewrite Hvi in Habs.
        by rewrite -Habs /is_in_stk Hget in Hx1.
      + split=> // x.
        have Hx: x = {| vtype := vtype x; vname := vname x |}.
          by case: x.
        (* Prove valid_stk: long! *)
        move: H6=> /(_ x).
        case Hget': (Mvar.get m.1 x)=> [getx|//].
        case Htypex: (vtype x)=> [ | |n'| ] //.
        + move=> H off Hoff.
          move: H=> /(_ off Hoff) [H /= H'].
          split=> //.
          by rewrite -(write_valid _ Hm').
          case Heq: ((v_var vi == x) && (i == off)).
          + move: Heq=> /andP [/eqP Heq /eqP Heqoff].
            rewrite Hx Htypex in Heq.
            move=> a0 Ha0 v1 Hv1.
            have ->: getx = get.
              have Hgeteq: Some getx = Some get.
                rewrite -Hget -Hget'.
                congr (_ _).
                by rewrite Hx Htypex -Heq Hvi.
              by move: Hgeteq=> [].
            rewrite (read_write_mem _ Hm') writeP Hvmem Heqoff add_repr_r [get + off]Z.add_comm eq_refl.
            rewrite -Hv1.
            rewrite /Array.set in Ht.
            case: ((0 <=? i) && (i <? Z.pos n)) Ht=> // Ht.
            move: Ht=> -[] // Ht.
            have ->: a0 = FArray.set a i (ok v0).
              rewrite Ht.
              admit.
            by rewrite Heqoff FArray.setP_eq.
          + admit.
        + (* here, x <> vi *)
          move=> [H H']; split.
          by rewrite -(write_valid _ Hm').
          move=> sv /= v1 Hv1.
          rewrite (read_write_mem _ Hm') writeP Hvmem.
          rewrite /sv Fv.setP_neq in Hv1.
          rewrite (H' v1 Hv1).
          case: ifP=> // Heq; exfalso.
          rewrite add_repr_r in Heq.
          have Heq': (get + i) = getx.
            apply (Z.add_cancel_l _ _ pstk).
            case: x Hx Hget' Htypex H' sv v1 Hv1=> [xt xn] Hx /= Hget' Htypex ????.
            rewrite Htypex in Hget'.
            rewrite [get + i]Z.add_comm.
            rewrite (get_valid_arepr Hget).
            rewrite (get_valid_wrepr Hget').
            rewrite [i + get]Z.add_comm.
            by apply/eqP.
            exact: (arr_set_ok Ht).
          have Habs: get + i != getx.
            apply: (var_stk_diff_off_l Hget Hget')=> //.
            rewrite vtype_diff //= Htypex //.
            exact: (arr_set_ok Ht).
          by rewrite Heq' eq_refl in Habs.
          by rewrite Hvi vtype_diff.
    move: He'=> /orP [/orP [He'|He']|He'].
    + case: e' He'=> // [] [] // [] // [] // z e' /andP [/eqP <- {z} He].
      rewrite /=.
      rewrite (check_eP He Hv Hvali) /= /sem_op2_i /mk_sem_sop2 /= Hi /=.
      exact: Hall.
    + case: e' He'=> // [][] // [] // e' [] // z.
      move=> /andP [/eqP <- {z} He].
      rewrite /= (check_eP He Hv Hvali) /= /sem_op2_i /mk_sem_sop2 /= Hi /=.
      rewrite [i + get]Z.add_comm.
      exact: Hall.
    + case: e Hvali He'=> // z /= []Hvali /eqP ->.
      rewrite -Hvali /= in Hi.
      move: Hi=> [] ->.
      exact: Hall.
  Admitted.

  Lemma check_memW (vi vi': var_i) (s1 s2: estate) v e e':
    check_var m vi vi' -> check_e m e e' -> valid s1 s2 -> forall s1', write_rval (Rmem vi e) v s1 = ok s1'->
    exists s2', write_rval (Rmem vi' e') v s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Hvar He Hv s1'.
    have Hv' := Hv.
    move: Hv'=> [] H1 H2 H3 H4 [H5 H6].
    apply: rbindP=> ptr.
    apply: rbindP=> vptr Hvptr Hptr.
    apply: rbindP=> off.
    apply: rbindP=> voff Hvoff Hoff.
    apply: rbindP=> val Hval.
    apply: rbindP=> m' Hm' []<-.
    rewrite /=.
    have ->: get_var (evm s2) vi' = ok vptr.
      rewrite -Hvptr.
      symmetry.
      apply/check_varP=> //.
    rewrite /= Hptr /=.
    rewrite (check_eP He Hv Hvoff) /= Hoff /= Hval /=.
    have Hvmem: valid_addr (emem s2) (I64.add ptr off).
      rewrite H3.
      apply/orP; left; apply/writeV; exists m'; exact: Hm'.
    have Hmem: exists m', write_mem (emem s2) (I64.add ptr off) val = ok m'.
      by apply/writeV.
    move: Hmem=> [m'2 Hm'2].
    rewrite Hm'2 /=.
    exists {| emem := m'2; evm := evm s2 |}; split=> //.
    split=> //=.
    + move=> w Hw.
      rewrite -(write_valid _ Hm') in Hw.
      exact: H1.
    + move=> w Hw.
      apply: read_mem_write_same.
      exact: Hm'.
      exact: Hm'2.
      exact: H2.
      by rewrite (write_valid _ Hm').
    + move=> w.
      rewrite -(write_valid _ Hm') -(write_valid _ Hm'2).
      exact: H3.
    + split=> //.
      move=> x.
      move: H6=> /(_ x).
      case Hget: (Mvar.get m.1 x)=> [getx|//].
      case Htypex: (vtype x)=> [ | |n| ] //.
      + move=> H off0 Hoff0.
        move: H=> /(_ off0 Hoff0) [H H'].
        split.
        by rewrite -(write_valid _ Hm'2).
        move=> t a Ht v0 Hv0.
        rewrite -(H' a Ht v0 Hv0).
        rewrite (read_write_mem _ Hm'2) writeP Hvmem.
        suff ->: I64.add ptr off == I64.repr (pstk + (off0 + getx)) = false=> //.
        apply/eqP=> Habs.
        have Hvalid1: valid_addr (emem s1) (I64.add ptr off).
          apply/writeV; exists m'; exact: Hm'.
        have := (H1 _ Hvalid1).
        rewrite Habs=> Habs'.
        apply: Habs'.
        move: (validm Hget)=> [sx [/= Hsz [Hsx Hsx' _]]].
        have Hx: x = {| vtype := sarr n; vname := vname x |}.
          rewrite -Htypex; clear; case: x=> //.
        rewrite Hx in Hget.
        rewrite -(get_valid_arepr Hget Hoff0).
        split.
        lia.
        rewrite Htypex /= in Hsz.
        move: Hsz=> [].
        lia.
      + move=> [H H']; split.
        by rewrite -(write_valid _ Hm'2).
        move=> sv v0 Hv0.
        rewrite -(H' v0 Hv0).
        rewrite (read_write_mem _ Hm'2) writeP Hvmem.
        suff ->: I64.add ptr off == I64.repr (pstk + getx) = false=> //.
        apply/eqP=> Habs.
        have Hvalid1: valid_addr (emem s1) (I64.add ptr off).
          apply/writeV; exists m'; exact: Hm'.
        have := (H1 _ Hvalid1).
        rewrite Habs=> Habs'.
        apply: Habs'.
        move: (validm Hget)=> [sx [/= Hsz [Hsx Hsx' _]]].
        have Hx: x = {| vtype := sword; vname := vname x |}.
          rewrite -Htypex; clear; case: x=> //.
        rewrite Hx in Hget.
        rewrite -(get_valid_wrepr Hget).
        split.
        lia.
        rewrite Htypex /= in Hsz.
        move: Hsz=> [].
        lia.
  Qed.

  Lemma check_arrW (vi vi': var_i) (s1 s2: estate) v e e':
    check_var m vi vi' -> check_e m e e' -> valid s1 s2 -> forall s1', write_rval (Raset vi e) v s1 = ok s1'->
    exists s2', write_rval (Raset vi' e') v s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Hvar He Hv s1'.
    have Hv' := Hv.
    move: Hv'=> [] H1 H2 H3 H4 [H5 H6].
    apply: rbindP=> [[]] // n a Ha.
    apply: rbindP=> i.
    apply: rbindP=> vali Hvali Hi.
    apply: rbindP=> v0 Hv0.
    apply: rbindP=> t Ht.
    apply: rbindP=> vm.
    apply: rbindP=> varr Hvarr []<- []<-.
    rewrite /=.
    rewrite (check_eP He Hv Hvali) /= Hv0 /= Hi /=.
    rewrite /on_arr_var.
    rewrite -(check_varP Hvar H4) Ha /= Ht /= /set_var.
    have Hvar' := Hvar; move: Hvar'=> /andP [/andP [Hnotinstk /eqP Heq] notstk].
    rewrite -Heq Hvarr /=.
    exists {| emem := emem s2; evm := (evm s2).[vi <- ok varr] |}; split=> //.
    split=> //=.
    + exact: eq_vm_write.
    + split=> //.
      rewrite /get_var Fv.setP_neq //.
      exact: valid_stk_write_notinstk.
  Qed.

  Lemma check_rvalP (r1 r2: rval) v (s1 s2: estate) :
    check_rval m r1 r2 -> valid s1 s2 ->
    forall s1', write_rval r1 v s1 = ok s1' ->
    exists s2', write_rval r2 v s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Hr Hv; move: Hr.
    case: r1=> [vi|vi|vi e|vi e].
    + case: r2=> // vi' /= _ s1' -[]<-.
      exists s2; split=> //.
    + case: r2=> // [vi'|vi' e].
      move=> /check_varW /(_ Hv) H s1' Hw.
      move: (H _ _ Hw)=> [s2' Hs2']; exists s2'=> //.
    + move=> /check_var_stkW /(_ Hv) H s1' Hw.
      move: (H _ _ Hw)=> [s2' Hs2']; exists s2'=> //.
    + case: r2=> // vi' e'.
      move=> /andP [Hvar He] s1' Hw.
      move: (check_memW Hvar He Hv Hw)=> [s2' Hs2']; exists s2'=> //.
    + case: r2=> // vi' e'.
      move=> /check_arr_stkW /(_ Hv) H s1' Hw.
      move: (H _ _ Hw)=> [s2' Hs2']; exists s2'=> //.
    + move=> /andP [Hvar He] s1' Hw.
      move: (check_arrW Hvar He Hv Hw)=> [s2' Hs2']; exists s2'=> //.
  Qed.

  Lemma check_rvalsP (r1 r2: rvals) vs (s1 s2: estate) :
    all2 (check_rval m) r1 r2 -> valid s1 s2 ->
    forall s1', write_rvals s1 r1 vs = ok s1' ->
    exists s2', write_rvals s2 r2 vs = ok s2' /\ valid s1' s2'.
  Proof.
    elim: r1 r2 vs s1 s2=> //= [|a l IH] [|a' l'] // [] //.
    + move=> ? s2 ? Hvalid s1' [] <-.
      exists s2; split=> //.
    + move=> vsa vsl s1 s2 /andP [Hchecka Hcheckl] Hvalid s1'.
      apply: rbindP=> x Ha Hl.
      move: (check_rvalP Hchecka Hvalid Ha)=> [s3 [Hs3 Hvalid']].
      move: (IH _ _ _ _ Hcheckl Hvalid' _ Hl)=> [s3' [Hs3' Hvalid'']].
      exists s3'; split=> //.
      by rewrite /= Hs3.
  Qed.

  Let Pi_r s1 (i1:instr_r) s2 :=
    forall ii1 ii2 i2, check_i m (MkI ii1 i1) (MkI ii2 i2) ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem_i SP s1' i2 s2' /\ valid s2 s2'.

  Let Pi s1 (i1:instr) s2 :=
    forall i2, check_i m i1 i2 ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem_I SP s1' i2 s2' /\ valid s2 s2'.

  Let Pc s1 (c1:cmd) s2 :=
    forall c2, all2 (check_i m) c1 c2 ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem SP s1' c2 s2' /\ valid s2 s2'.

  Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.

  Let Pfun (m1: mem) (fn: funname) (vargs: seq value) (m2: mem) (vres: seq value) := True.

  Local Lemma Hskip s: Pc s [::] s.
  Proof.
    move=> [] // => _ s' Hv.
    exists s'; split; [exact: S.Eskip|exact: Hv].
  Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I P s1 i s2 ->
    Pi s1 i s2 -> sem P s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> _ Hi _ Hc [|i' c'] //= /andP [Hi'c Hc'c] s1' Hv.
    have [s2' [Hi' Hv2]] := Hi _ Hi'c _ Hv.
    have [s3' [Hc' Hv3]] := Hc _ Hc'c _ Hv2.
    exists s3'; split=> //.
    apply: S.Eseq; [exact: Hi'|exact: Hc'].
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i P s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. 
    move=> _ Hi [ii' ir'] Hc s1' Hv.
    move: Hi=> /(_ ii ii' ir' Hc s1' Hv) [s2' [Hs2'1 Hs2'2]].
    by exists s2'; split.
  Qed.

  Local Lemma Hassgn s1 s2 x tag e :
    Let v := sem_pexpr s1 e in write_rval x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.
  Proof.
    apply: rbindP=> v Hv Hw ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= x' a e' /andP [Hrval He].
    have He_eq := (check_eP He Hvalid Hv).
    move: (check_rvalP Hrval Hvalid Hw)=> [s2' [Hw' Hvalid']].
    exists s2'; split=> //.
    apply: S.Eassgn.
    by rewrite He_eq.
  Qed.

  Local Lemma Hopn s1 s2 o xs es :
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_rvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    apply: rbindP=> vs.
    apply: rbindP=> w He Hop Hw ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= xs' o' es' /andP [/andP [Hrvals /eqP Ho] Hes].
    have Hes_eq := (check_esP Hes Hvalid).
    move: (check_rvalsP Hrvals Hvalid Hw)=> [s2' [Hw' Hvalid']].
    exists s2'; split=> //.
    apply: S.Eopn.
    by rewrite (Hes_eq _ He) /= -Ho Hop /= Hw'.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem P s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP=> v Hv Htrue ? Hc ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c1' c2' /andP [/andP [He Hcheck] _].
    move: (Hc _ Hcheck _ Hvalid)=> [s2' [Hsem Hvalid']].
    exists s2'; split=> //.
    apply: S.Eif_true=> //.
    by rewrite (check_eP He Hvalid Hv).
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem P s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP=> v Hv Hfalse ? Hc ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c1' c2' /andP [/andP [He _] Hcheck].
    move: (Hc _ Hcheck _ Hvalid)=> [s2' [Hsem Hvalid']].
    exists s2'; split=> //.
    apply: S.Eif_false=> //.
    by rewrite (check_eP He Hvalid Hv).
  Qed.

  Local Lemma Hwhile_true s1 s2 s3 e c :
    Let x := sem_pexpr s1 e in to_bool x = ok true ->
    sem P s1 c s2 -> Pc s1 c s2 ->
    sem_i P s2 (Cwhile e c) s3 -> Pi_r s2 (Cwhile e c) s3 -> Pi_r s1 (Cwhile e c) s3.
  Proof.
    apply: rbindP=> v Hv Htrue ? Hc ? Hwhile ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c' /andP [He Hi].
    move: (Hc _ Hi _ Hvalid)=> [s2' [Hsem' Hvalid']].
    have [|s3' [Hsem'' Hvalid'']] := (Hwhile ii1 ii2 (Cwhile e' c') _ _ Hvalid').
    by rewrite /= He Hi.
    exists s3'; split=> //.
    apply: S.Ewhile_true.
    by rewrite (check_eP He Hvalid Hv).
    exact: Hsem'.
    exact: Hsem''.
  Qed.

  Local Lemma Hwhile_false s e c :
    Let x := sem_pexpr s e in to_bool x = ok false ->
    Pi_r s (Cwhile e c) s.
  Proof.
    apply: rbindP=> v Hv Hfalse ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c' /andP [He _].
    exists s1'; split=> //.
    apply: S.Ewhile_false.
    by rewrite (check_eP He Hvalid Hv).
  Qed.

  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for P i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof. by []. Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof. by []. Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem P s1' c s2 ->
    Pc s1' c s2 ->
    sem_for P i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof. by []. Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs s1 args = Ok error vargs ->
    sem_call P (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_rvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof. by []. Qed.

  Local Lemma Hproc m1 m2 fn f vargs s1 vm2 vres:
    get_fundef P fn = Some f ->
    write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem P s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
    List.Forall is_full_array vres ->
    Pfun m1 fn vargs m2 vres.
  Proof. by []. Qed.

  Lemma check_cP s1 c1 s2: sem P s1 c1 s2 -> Pc s1 c1 s2.
  Proof.
    apply (@sem_Ind P Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.
End PROOF.

Definition check_fd (l:list (var * Z))
    (fd: fundef) (fd': S.sfundef) :=
  match init_map (S.sf_stk_sz fd') (S.sf_stk_id fd') l with 
  | Ok m =>
     all2 (check_i m) (f_body fd) (S.sf_body fd')
  | _ => false
  end.

Definition init_vm mem pstk (l : seq.seq (var * Z)) vm :=
  let add (vm : vmap) (vp : var * Z) := 
    match vtype vp.1 with
    | sword => 
      let w := Result.default I64.zero (Memory.read_mem mem (I64.repr (pstk + vp.2))) in
      vm.[{|vtype := sword; vname := vname vp.1 |} <- ok w]
    | _ => vm 
      end in
  foldl add vm l.

(*
Lemma init_mapP nstk pstk l sz m vm m1 m2 :
  alloc_stack m1 sz = ok (pstk, m2) -> 
  init_map sz nstk l = Ok unit m -> 
  all_empty_arr vm ->
  [/\ valid_map m sz, m.2 = nstk, all_empty_arr (init_vm m2 pstk l vm) &
  valid m sz pstk 
    {| emem := m1; evm := init_vm m2 pstk l vm |}
    {| emem := m2; evm := vm.[{|vtype := sword;vname := nstk|} <- pstk]|}].
Proof.
  move=> /alloc_stackP [Hadd Hread Hval Hbound].
  rewrite /init_map /init_vm.
  set f1 := (f in foldM f _ _ ).
  set f2 := (f in foldl f vm _).
  set g := (g in foldM _ _ _ >>= g). 
  have : forall p p', 
    foldM f1 p l = Ok unit p' -> 
    valid_map (p.1,nstk) p.2 -> 0 <= p.2 ->
    (forall y py sy, Mvar.get p.1 y = Some py ->
        size_of (vtype y) = Ok unit sy -> py + sy <= p.2) ->
    [/\ p.2 <= p'.2, 
        valid_map (p'.1, nstk) p'.2 &
    forall vm1, 
      p'.2 <= sz ->
      all_empty_arr vm1 ->
      valid (p.1, nstk) sz pstk {| emem := m1; evm := vm1 |}
         {| emem := m2; evm := vm.[{| vtype := sword; vname := nstk |} <- pstk] |} ->
      all_empty_arr (foldl f2 vm1 l) /\ 
      valid (p'.1, nstk) sz pstk {| emem := m1; evm := foldl f2 vm1 l |}
            {| emem := m2; evm := vm.[{| vtype := sword; vname := nstk |} <- pstk] |}].
  + elim:l => [|vp l Hrec] p p'//=.
    + by move=>[] <- ???;split=>//;omega.
    rewrite {2}/f1;case:ifPn=> //= /Z.leb_le Hle.
    case Hs : size_of=> [svp|]//= /Hrec /= {Hrec}Hrec H2 H3 H4. 
    have Hpos := size_of_pos Hs.
    case:Hrec.
    + move=> x px;rewrite Mvar.setP;case:ifPn => /eqP Heq.
      + move=> [] ?;subst;exists svp;split=>//;split.
        + omega. + omega.
        move=> y py sy Hne.
        by rewrite Mvar.setP_neq // => /H4 H /H ?;omega.
      move=> /H2 [sx] [Hsx] [] Hle0 Hpx Hy;exists sx;split=>//;split=>//.
      + omega.
      move=> y py sy Hne;rewrite Mvar.setP;case:eqP=> [?[]? |].
      + subst;rewrite Hs => -[] ?;subst; omega.
      by move=> Hney;apply Hy.
    + omega.
    + move=> y py sy;rewrite Mvar.setP;case:eqP=> [?[]?|].
      + subst;rewrite Hs => -[] ->;omega.
      move=> ? /H4 H /H ?;omega.
    move=> Hle2 H' Hvm;split=>//;first by omega.
    move=> vm1 Hsz Hall Hvm1.
    rewrite {2 4}/f2; case Ht : (vtype vp.1) Hs => [|||n]//=.
    + move=> [] ?;subst svp.
      have := Hval (I64.repr (pstk + vp.2)).
      have -> : (pstk <=? I64.repr (pstk + vp.2)) &&
                  (I64.repr (pstk + vp.2) <? pstk + sz).
      + rewrite I64.unsigned_repr /I64.max_unsigned.
        + by apply /andP;split;[apply /Z.leb_le | apply /Z.ltb_lt];omega.  
        by have ?:= I64.unsigned_range pstk;omega.
      rewrite orbC /= => /readV [w] Hr; rewrite Hr /=;apply Hvm=> // {Hvm f1 f2 g}.
      + move=> z;case ({|vtype := sword; vname := vname vp.1|} =P z) => [<- | /eqP ?].
        + by rewrite Fv.setP_eq.
        by rewrite Fv.setP_neq.
      case: Hvm1=> /= W0 W1 W5 W2 [W3 W4];split=> //=.
      + move=> x;rewrite /is_in_stk;rewrite Mvar.setP. 
        case:eqP => // /eqP HH ??;rewrite Fv.setP_neq;first by apply W2.
        by rewrite -Ht;case: (vp.1) HH.
      split=> //.
      move=> x;rewrite Mvar.setP;case:eqP=> [<- | /eqP Hne].
      + by rewrite Ht Fv.setP_eq.
      have /= := W4 x;case: Mvar.get => //= a;case Htx: (vtype x)=> [|||p1]//=.
      + rewrite Fv.setP_neq //.
        by move: Hne;rewrite (var_surj vp.1) (var_surj x) Ht Htx .
      by rewrite Fv.setP_neq.
    move=> [] ?;subst svp. 
    apply Hvm =>//. 
    case: Hvm1=> /= W0 W1 W5 W2 [W3 W4];split=> //=.
    + move=> x;rewrite /is_in_stk;rewrite Mvar.setP. 
      by case:eqP => // /eqP HH ??;apply W2.
    split=>//.
    move=> x;rewrite Mvar.setP;case:eqP=> [<- | /eqP Hne].
    + rewrite Ht /= => w0 Hw0. 
      have := Hval (I64.repr (pstk + (w0 + vp.2))).
      have -> :  (pstk <=? I64.repr (pstk + (w0 + vp.2))) &&
                   (I64.repr (pstk + (w0 + vp.2)) <? pstk + sz).
      + rewrite I64.unsigned_repr.
        + by apply /andP;split;[apply /Z.leb_le | apply Z.ltb_lt];omega. 
        by rewrite /I64.max_unsigned;have ?:= I64.unsigned_range pstk;omega.
      rewrite orbC /= => /readV [w' Hw'];rewrite Hw' /=.
      split;first by apply /readV;exists w'.
      move=> v. rewrite (Hall {| vtype := sarr n; vname := vname vp.1 |}).
      by rewrite /Array.empty.
    have /= := W4 x;case: Mvar.get => //= a;case Htx: (vtype x)=> [|||p1]//=.
  move=> H;case Heq : foldM => [p'|]//=.
  case: (H _ _ Heq)=> //= Hp' Hv Hvm1.
  rewrite /g;case:ifP => //= /Z.leb_le Hp [] <- /= Hall.
  have [| Hall1 Hval1]:= Hvm1 _ Hp Hall.
  + split => //=;first by move=> x ??;rewrite Fv.setP_neq // eq_sym.
    by split=>//=;rewrite Fv.setP_eq.
  split=>// x px Hx.
  case :(Hv x px Hx) => //= sx [] Hsx [] H1 H2 H3.
  by exists sx;split=>//;split=>//;omega.
Qed.
*)

(*
Lemma check_fdP ta tr l (fd:fundef ta tr) fd':
  check_fd l fd fd' ->
  forall m1 va m1' vr, 
    sem_call m1 fd va m1' vr ->
    (exists p, alloc_stack m1 (S.fd_stk_size fd') = ok p) ->
    S.sem_call m1 fd' va m1' vr.
Proof.
  rewrite /check_fd. 
  case Hinit: init_map => [m|] //=.
  move=> /andP[]/andP[]/andP[] Hcxa /eqb_rvalP[]_ Hexa /andP[] Hcr /eqb_rvalP[]_ Her Hcb.
  move=> m1 va m1' vr H;sinversion H;sinversion H0=> -[[pstk m2] Halloc].
  econstructor;eauto => vm0 Hvm0.
  have [/= Hv Hestk Hall Hval] := init_mapP Halloc Hinit Hvm0.
  have [vm2 /= [Hsem Heq]] := H6 _ Hall.
  rewrite -Hexa -Her.
  pose nstk := S.fd_nstk fd'.
  pose s2 := {| emem := m2;
                 evm := write_rval vm0.[{| vtype := sword; vname := nstk |} <- pstk]
                           (fd_arg fd) va |}.
  have /= {Hval}Hval := valid_write_rval va Hcxa Hval.
  have [|[m2' vm2'] [Hsem' Hval']]:= check_cP _ Hv Hcb Hval Hsem.
  + by have []:= alloc_stackP Halloc.
  exists vm2', m2';split=> //.
  + case Hval' => _ _ _ H _.
    have := sem_rval2pe (fd_res fd) vm2'.
    by rewrite -(check_eP H Hcr) (sem_rval2pe (fd_res fd) vm2) Heq => -[].
  apply eq_memP=> w.
  pose sz := S.fd_stk_size fd'.
  have -> := @free_stackP m2' (free_stack m2' pstk sz) pstk sz (erefl _) w.
  case Hval' => /=;rewrite /disjoint_stk => Hdisj Hmem Hvalw _ _.
  move: (Hdisj w) (Hmem w) (Hvalw w)=> {Hdisj Hmem Hval Hvalw} Hdisjw Hmemw Hvalw.
  case Heq1: (read_mem m1' w) => [w'|].
  + have Hw : valid_addr m1' w by apply /readV;exists w'.
    have -> : ((pstk <=? w) && (w <? pstk + sz))=false. 
    + by apply /negbTE /negP => /andP[] /Z.leb_le ? /Z.ltb_lt ?;apply Hdisjw.
    by rewrite -Heq1;apply Hmemw.
  have ? := read_mem_error Heq1;subst;case:ifP=> Hbound //.
  case Heq2: (read_mem m2' w) => [w'|];last by rewrite (read_mem_error Heq2).
  have : valid_addr m2' w by apply /readV;exists w'.
  by rewrite Hvalw Hbound orbC /= => /readV [w1];rewrite Heq1.
Qed.
*)
