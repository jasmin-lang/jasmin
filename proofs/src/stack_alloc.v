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

Definition is_vstk (m:map) (x:var_i) := 
  (vname x == m.2) && (vtype x == sword).

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

Definition check_arr_stk (m:map) (x1:var_i) (e1:pexpr) (x2:var_i) (e2:pexpr) := 
  is_vstk m x2 && is_arr_type (vtype x1) &&
    match Mvar.get m.1 x1 with
    | Some ofs => 
      (e2 == Pcast (Papp2 Oadd (Pconst ofs) e1)) || 
      (e2 == Pcast (Papp2 Oadd e1 (Pconst ofs))) ||
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
  | Pget  x1 e1, Pload x2 e2 => check_arr_stk m x1 e1 x2 e2
  | Pload x1 e1, Pload x2 e2 => check_var m x1 x2 && check_e m e1 e2
  | Pnot   e1, Pnot   e2 => check_e m e1 e2 
  | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
    (o1 == o2) && check_e m e11 e21 && check_e m e12 e22
  | _, _ => false
  end.

Definition check_rval (m:map) (r1 r2:rval) := 
  match r1, r2 with
  | Rnone _, Rnone _ => true
  | Rvar x1, Rvar x2 => check_var m x1 x2
  | Rvar x1, Rmem x2 e2 => check_var_stk m x1 x2 e2
  | Rmem x1 e1, Rmem x2 e2 => 
    (check_var m x1 x2 && check_e m e1 e2) || check_arr_stk m x1 e1 x2 e2
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
              forall v, FArray.get a (I64.repr off) = ok v ->
                read_mem m2 (I64.repr (pstk + (off + p))) = ok v
        | _ => True
        end
      | _ => True
      end.

  Definition eq_vm (vm1 vm2:vmap) := 
    (forall (x:var), ~~is_in_stk m x -> x != vstk m -> vm1.[x] = vm2.[x]).

  Definition disjoint_stk m := 
    forall w, valid_addr m w -> ~(pstk <= w < pstk + stk_size).

  Definition valid (s1 s2:estate) :=
    [/\ disjoint_stk (emem s1), 
        (forall w, valid_addr (emem s1) w -> read_mem (emem s1) w = read_mem (emem s2) w),
        (forall w, valid_addr (emem s2) w = valid_addr (emem s1) w ||  
                                       ((pstk <=? w) && (w <? pstk + stk_size))),
        eq_vm (evm s1) (evm s2) & 
        (evm s2).[{|vtype:= sword; vname := m.2|}] = ok pstk /\
        valid_stk (evm s1) (emem s2) pstk ].

  Lemma check_eP (e1 e2: pexpr) (s1 s2: estate) :
    check_e m e1 e2 -> valid s1 s2 -> sem_pexpr s1 e1 = sem_pexpr s2 e2.
  Admitted.

  Lemma check_esP (es es': pexprs) (s1 s2: estate) :
    all2 (check_e m) es es' -> valid s1 s2 -> sem_pexprs s1 es = sem_pexprs s2 es'.
  Admitted.

  Lemma check_rvalP (r1 r2: rval) v (s1 s2: estate) :
    check_rval m r1 r2 -> valid s1 s2 ->
    forall s1', write_rval r1 v s1 = ok s1' ->
    exists s2', write_rval r2 v s2 = ok s2' /\ valid s1' s2'.
  Admitted.

  Lemma check_rvalsP (r1 r2: rvals) vs (s1 s2: estate) :
    all2 (check_rval m) r1 r2 -> valid s1 s2 ->
    forall s1', write_rvals s1 r1 vs = ok s1' ->
    exists s2', write_rvals s2 r2 vs = ok s2' /\ valid s1' s2'.
  Admitted.

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

  (*
  Lemma check_bcmd1P i s1 s1' s2 : 
    valid s1 s2 -> 
    check_bcmd1 m i ->
    sem_bcmd s1 i = ok s1' ->
    exists s2', sem_bcmd s2 i = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Hv;have Hvm : eq_vm (evm s1) (evm s2) by case Hv.
    case: i=> [? x e | x e | e1 e2]/= /andP[]H1 H2.
    + case Heq : (sem_pexpr _ e) => [v|] //= [] ?;subst s1'.
      exists {| emem := emem s2; evm := write_rval (evm s2) x v |}.
      by rewrite -(check_eP Hvm H2) Heq;split => //; apply valid_write_rval.
    + case Heq : sem_pexpr => [v|] //=.
      case Heqr : read_mem => [w|] //= [] <-.
      exists {| emem := emem s2; evm := write_rval (evm s2) x w |}.
      rewrite -(check_eP Hvm H2) Heq /=.
      case:(Hv) Heqr=> _ Hmem _ _ _ H;rewrite -Hmem ?H /=.
      + by split=> //;apply valid_write_rval.
      by apply /readV;exists w.
    case Heq1: (sem_pexpr _ e1) => [v1|] //=.
    case Heq2: (sem_pexpr _ e2) => [v2|] //=.
    case Heq3: write_mem => [m'|] //= [] <-.
    have H1v1: valid_addr (emem s1) v1 by apply /(writeV _ _ v2);exists m'.
    have H2v1: valid_addr (emem s2) v1.
    + case: Hv => _ Hr _ _ _.
      by have Heq := Hr _ H1v1;apply /readV;rewrite -Heq;apply /readV.
    have [m2' Hm2'] : exists m2', write_mem (emem s2) v1 v2 = ok m2' by apply/writeV. 
    exists {|emem := m2'; evm := evm s2|}. 
    rewrite -(check_eP Hvm H1) -(check_eP Hvm H2) Heq1 Heq2 /= Hm2' /=;split=>//.
    case: Hv {Hvm H1 H2 Heq1 Heq2} => [H0 H1 HH H2 [H3 H4]];split => //=.
    + move=> w;rewrite -(write_valid w Heq3);apply H0.
    + move=> w;rewrite -(write_valid w Heq3) => Hw.  
      rewrite (read_write_mem _ Heq3) (read_write_mem _ Hm2').
      by rewrite !memory.writeP H1v1 H2v1 H1.
    + by move=> w;rewrite -(write_valid _ Hm2') HH (write_valid _ Heq3).
    split => //.
    move=> z; have := H4 z.
    case Heq: Mvar.get => [p|]//.
    move: (pstk_add) (I64.unsigned_range pstk);rewrite /stk_ok=> ??. 
    case Heqt : vtype => [||| n]//=. 
    + rewrite (read_write_mem _ Hm2') memory.writeP.
      have -> : valid_addr (emem s2) v1.
      + by apply /(writeV (emem s2) v1 v2);exists m2'.
      case: eqP=> //= ?;subst v1;have [sz]:= validm Heq.
      rewrite Heqt /= => -[] [] ?;subst sz=> -[] ?? H.
      have := H0 _ H1v1;rewrite I64.unsigned_repr=> [[]|];first by omega.
      by rewrite /I64.max_unsigned; omega.
    move=> H4' x Hx;have [Hval Hget]:= H4' _ Hx;split.
    + by rewrite -(write_valid _ Hm2').
    move:Hget;rewrite (read_write_mem _ Hm2') memory.writeP.
    have -> : valid_addr (emem s2) v1.
    + by apply /(writeV (emem s2) v1 v2);exists m2'.
    case:eqP => // H.
    subst v1;have [sz]:= validm Heq.
    rewrite Heqt /= => -[] [] ?;subst sz=> -[] ?? H.
    have := H0 _ H1v1;rewrite I64.unsigned_repr=> [[]|];first by omega.
    by rewrite /I64.max_unsigned; omega.
  Qed.
  *)

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

  (*
  Lemma is_varP t (e:pexpr) x :
     is_var e = Some x -> t = vtype x /\ JMeq e (Pvar x).
  Proof. by case: e => //= ? [] ->. Qed.

  Lemma check_setP x t1 (e1:pexpr t1) e e2 :  
    check_set m x e1 e e2 ->
    exists n nx' ep p,
    let x' := {|vtype := sarr n; vname := nx'|} in
    [/\ t1 = sarr n, x = x', 
        JMeq e1 (Papp3 (Oset n) (Pvar x') ep e2), 
        Mvar.get m.1 x = Some p &
        [/\ e = sadd (estk m) (sadd ep (Pconst p)),
            check_e m ep & check_e m e2 ]].
  Proof.
    case: e1=> //= ???? [] //= n e1 ep e2'.
    case Heq1 :is_var => [[? nx']|] //=.
    have [/=?]:= is_varP Heq1;subst=> {Heq1} ->.
    move=> /andP[]/andP[]/andP[]/andP[]/eqP ->.
    move=> /eqb_pexprP[] _ -> ??.
    case Heq: Mvar.get => [p|] //= /eqb_pexprP []_ ->.
    by exists n, nx', ep, p.
  Qed.
  *)

  Lemma add_repr_r x y : I64.add x (I64.repr y) = I64.repr (x + y).
  Proof.
    by apply: reqP; rewrite !urepr !I64.Z_mod_modulus_eq Zplus_mod_idemp_r eq_refl.
  Qed.

  (*
  Lemma check_bcmd2P i1 i2 s1 s1' s2 : 
    valid s1 s2 -> 
    check_bcmd2 m i1 i2 ->
    sem_bcmd s1 i1 = ok s1' ->
    exists s2', sem_bcmd s2 i2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Hv;have Hvm : eq_vm (evm s1) (evm s2) by case Hv.
    case: i1 i2=> [?[[xt1 x1]|]e1|x1 e1|e11 e12]//= [? x2 e2|x2 e2|e21 e22] //=.
    set X1 := {|vtype := _; vname := _|};move=> /orP[/andP[]/andP[]|].
    + move=> /eqb_pexprP[]?;subst=> -> H2;rewrite -(check_eP Hvm H2).
      rewrite /check_assgn /check_add;case Hgetx: Mvar.get => [p|]//=.
      move=> /eqb_pexprP [] _ ->;case: sem_pexpr => [v22|]//= [] <-.
      have : sem_pexpr (evm s2) (Papp2 Oadd (estk m) p) = 
             ok (I64.repr (pstk + p)).
      + by case Hv=>/= ????[->?];rewrite add_repr_r.
      move=> /saddP -> /=; have /(writeV _ _ v22) [m2' Hm2'] := get_valid_word Hv Hgetx.
      rewrite Hm2' /=;eexists;split;[eauto | ].
      case: (Hv)=> {H2 e1 e21 e22 Hvm} H0 H1 HH H2 [H3 H4];split => //=.
      + move=> w Hw;rewrite H1 // (read_write_mem w Hm2').
        rewrite memory.writeP (get_valid_word Hv Hgetx).
        case: eqP => // ?;subst w.
        have := H0 _ Hw;rewrite -(get_valid_wrepr Hgetx)=> ?.
        by have [sx /= [][]<-[]?? _]:= validm Hgetx;omega.
      + by move=> w;rewrite -(write_valid _ Hm2').
      + move=> z Hz;rewrite Fv.setP_neq;first by apply H2.
        by apply: contra Hz => /eqP <-;rewrite /is_in_stk Hgetx.
      split=>//.
      move=> z;have := H4 z;case Hgetz: Mvar.get => [pz|] //=.
      case Heqt: (vtype z)=> [||| n] //=.
      case: z Heqt Hgetz=> tz z /= -> Hgetz.
      + rewrite (read_write_mem (I64.repr (pstk + pz)) Hm2') memory.writeP.
        rewrite (get_valid_word Hv Hgetx)=> ->.
        case: eqP=> // Heqr.
        + have : I64.unsigned (I64.repr (pstk + pz)) = I64.repr (pstk + p).
          + by rewrite Heqr.
          rewrite -(get_valid_wrepr Hgetx) -(get_valid_wrepr Hgetz).
          rewrite Z.add_cancel_l=> ?;subst pz.
          case: (X1 =P {| vtype := sword; vname := z |}) => [[] <-|/eqP Hne].
          + by rewrite Fv.setP_eq.
          have [sx /=[][]<-[]??/(_ _ _ _ Hne Hgetz (erefl _)) ?]:= validm Hgetx.
          omega.
        rewrite Fv.setP_neq //;apply /negP=> /eqP H;apply Heqr.
        by move: Hgetx;rewrite H Hgetz=> -[] ->.
      case: z Hgetz Heqt=> tz z /= Hgetz ?;subst tz=> H p1 Hp1.
      rewrite (read_write_mem (I64.repr (pstk + (p1 + pz))) Hm2') memory.writeP.
      have [Hval Hget]:= H _ Hp1;split;first by rewrite -(write_valid _ Hm2').
      rewrite (get_valid_word Hv Hgetx).
      case: eqP=> // Heqr;last by rewrite Fv.setP_neq.
      have : I64.unsigned (I64.repr (pstk + (p1 + pz))) = I64.repr (pstk + p).
      + by rewrite Heqr.
      rewrite -(get_valid_wrepr Hgetx) -(get_valid_arepr Hgetz) // => ?.
      have [sx /=[][]<-[]??/(_ _ _ _ _ Hgetz (erefl _))]:= validm Hgetx.
      by move=> /(_ isT) ??; omega.
    move=> /check_setP [n [nx' [ep [p]]]] /= [] ?;subst=> -[] ?;subst.
    move=> -> Hgetx []-> /= Hep He22.
    rewrite (check_eP Hvm Hep) (check_eP Hvm He22).
    case Heqp: (sem_pexpr _ ep) => [vep|] //=.
    case Heq2: (sem_pexpr _ e22) => [ve2|] //=.
    rewrite /Array.set;case:ifP => //=.
    move=> /andP[] /Z.leb_le Hle1 /Z.ltb_lt Hlt1 [] <-.
    have : sem_pexpr (evm s2) (Papp2 Oadd ep p) = ok (I64.repr (vep + p)).
    + by rewrite /= Heqp /= add_repr_r.
    move=> /saddP Heqa.
    have : sem_pexpr (evm s2) (Papp2 Oadd (estk m) (sadd ep p)) = 
           ok (I64.repr (pstk + (vep + p))).
    + by rewrite /= Heqa /= add_repr_r;case: Hv => ????[-> ?].
    move=> /saddP -> /=.
    have Hvep: 0 <= vep < Z.pos n by [].
    have  /(writeV _ _ ve2) [m2' Hm2']:= get_valid_arr Hv Hgetx Hvep.  
    rewrite Hm2' /=;eexists;split;[eauto | ].
    have Hvp : valid_addr (emem s2) (I64.repr (pstk + (vep + p))).
    + by apply /writeV;eauto.
    case: (Hv)=> {Hep He22 Heq2 Heqp e1 e21 e22 Hvm} H0 H1 HH H2 [H3 H4];split => //=.
    + move=> w Hw;rewrite H1 // (read_write_mem w Hm2').
      rewrite memory.writeP Hvp;case: eqP => // ?;subst w.
      have := H0 _ Hw;rewrite -(get_valid_arepr Hgetx Hvep) => ?. 
      by have [sx /= [][]<-[]?? _]:= validm Hgetx;omega.
    + by move=> w;rewrite -(write_valid _ Hm2').
    + move=> z Hz;rewrite Fv.setP_neq;first by apply H2.
      by apply: contra Hz => /eqP <-;rewrite /is_in_stk Hgetx.
    split=>//.
    move=> z;have := H4 z;case Hgetz: Mvar.get => [pz|] //=.
    case Heqt: (vtype z)=> [||| n'] //=.
    + case: z Heqt Hgetz=> tz z /= -> Hgetz.
      rewrite (read_write_mem _ Hm2') memory.writeP Hvp => ->.
      case: eqP=> // Heqr;last by rewrite Fv.setP_neq.
      have : I64.unsigned (I64.repr (pstk + pz)) = 
                     I64.repr (pstk + (vep + p)).
      + by rewrite -Heqr.
      rewrite -(get_valid_arepr Hgetx)// -(get_valid_wrepr Hgetz) // => ?.
      have [sx /=[][]<-[]??/(_ _ _ _ _ Hgetz (erefl _))]:= validm Hgetx.
      move=> /(_ isT) ?;omega.
    case: z Hgetz Heqt=> tz z /= Hgetz ?;subst tz=> H p1 Hp1.
    rewrite (read_write_mem _ Hm2') memory.writeP Hvp.
    have [Hval Hget] := (H _ Hp1);split;first by rewrite -(write_valid _ Hm2').
    case: eqP=> // Heqr.
    + have: I64.unsigned (I64.repr (pstk + (p1 + pz))) = 
            I64.repr (pstk + (vep + p)).
      + by rewrite -Heqr.
      rewrite -(get_valid_arepr Hgetx)// -(get_valid_arepr Hgetz)//= => Heq.
      case: (X1 =P  {| vtype := sarr n'; vname := z |})=> [[]??|/eqP Hne].
      + subst;rewrite Fv.setP_eq.
        move: Hgetx;rewrite Hgetz => -[] ?; subst pz.
        have -> : p1 = vep by omega.
        by rewrite I64.repr_unsigned FArray.setP_eq.
      have [sx[][]<-[]??/(_ _ _ _ Hne Hgetz (erefl _)) ???]:= validm Hgetx.       
      by omega.
    case: (X1 =P  {| vtype := sarr n'; vname := z |})=> [[]??|/eqP Hne];
      last by rewrite Fv.setP_neq.
    subst n' nx';rewrite Fv.setP_eq FArray.setP_neq //.
    apply /negP=> /eqP HH1;have ? : p1 = vep.
    + rewrite HH1 I64.unsigned_repr // /I64.max_unsigned.
      have [sz [][]<-[]?? _]:= validm Hgetz.
      move: pstk_add (I64.unsigned_range pstk);rewrite /stk_ok=> ??. 
      omega.
    by subst p1;apply Heqr;move: Hgetx;rewrite Hgetz=> -[] <-.
  Qed.
  *)

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
    have He_eq := (check_eP He Hvalid).
    move: (check_rvalP Hrval Hvalid Hw)=> [s2' [Hw' Hvalid']].
    exists s2'; split=> //.
    apply: S.Eassgn.
    by rewrite -He_eq Hv.
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
    by rewrite -Hes_eq He /= -Ho Hop /= Hw'.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem P s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> ? ? Hc ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c1' c2' /andP [/andP [He Htrue] _].
    move: (Hc _ Htrue _ Hvalid)=> [s2' [Hsem Hvalid']].
    exists s2'; split=> //.
    apply: S.Eif_true=> //.
    by rewrite -(check_eP He Hvalid).
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem P s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> ? ? Hc ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c1' c2' /andP [/andP [He _] Hfalse].
    move: (Hc _ Hfalse _ Hvalid)=> [s2' [Hsem Hvalid']].
    exists s2'; split=> //.
    apply: S.Eif_false=> //.
    by rewrite -(check_eP He Hvalid).
  Qed.

  Local Lemma Hwhile_true s1 s2 s3 e c :
    Let x := sem_pexpr s1 e in to_bool x = ok true ->
    sem P s1 c s2 -> Pc s1 c s2 ->
    sem_i P s2 (Cwhile e c) s3 -> Pi_r s2 (Cwhile e c) s3 -> Pi_r s1 (Cwhile e c) s3.
  Proof.
    move=> Htrue ? Hc ? Hwhile ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c' /andP [He Hi].
    move: (Hc _ Hi _ Hvalid)=> [s2' [Hsem' Hvalid']].
    have [|s3' [Hsem'' Hvalid'']] := (Hwhile ii1 ii2 (Cwhile e' c') _ _ Hvalid').
    by rewrite /= He Hi.
    exists s3'; split=> //.
    apply: S.Ewhile_true.
    rewrite (check_eP He Hvalid) in Htrue.
    exact: Htrue.
    exact: Hsem'.
    exact: Hsem''.
  Qed.

  Local Lemma Hwhile_false s e c :
    Let x := sem_pexpr s e in to_bool x = ok false ->
    Pi_r s (Cwhile e c) s.
  Proof.
    move=> Hfalse ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c' /andP [He _].
    exists s1'; split=> //.
    apply: S.Ewhile_false.
    rewrite -(check_eP He Hvalid).
    exact: Hfalse.
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

Lemma size_of_pos t s : size_of t = ok s -> 1 <= s.
Proof. case: t=> //= [p [] <-|[] <-] //=; zify; omega. Qed.

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
