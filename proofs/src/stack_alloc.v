(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import JMeq.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr memory dmasm_sem.
Require Import constant_prop.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Definition map := (Mvar.t Z * Ident.ident)%type.

Definition size_of (t:stype) := 
  match t with
  | sword        => Ok unit 1%Z
  | sarr n sword => Ok unit (Zpos n)
  | _            => Error tt
  end.

Definition init_map stk (l:list (var * Z)) sz:=
  let add (vp:var*Z) (mp:Mvar.t Z * Z) :=
    if (mp.2 <=? vp.2)%Z then 
      size_of (vtype vp.1) >>= (fun s =>
      Ok unit (Mvar.set mp.1 vp.1 vp.2, vp.2 + s)%Z)
    else Error tt in
  foldM add (Mvar.empty Z, 0%Z) l >>= (fun mp =>
    if (mp.2 <=? sz)%Z then Ok unit (mp.1, vname stk)
    else Error tt).

Definition is_in_stk (m:map) (x:var) := 
  match Mvar.get m.1 x with 
  | Some _ => true
  | None   => false
  end.

Fixpoint check_e (m:map) t (e:pexpr t) := 
  match e with
  | Pvar x => ~~(is_in_stk m x || (vname x == m.2))
  | Pconst _ => true
  | Pbool  _ => true
  | Papp1 _ _ _ e1 => check_e m e1
  | Papp2 _ _ _ _ e1 e2 => check_e m e1 && check_e m e2
  | Papp3 _ _ _ _ _ e1 e2 e3 => check_e m e1 && check_e m e2 && check_e m e3
  end.

Fixpoint check_rval (m:map) t (x:rval t) := 
  match x with 
  | Rvar x          => ~~(is_in_stk m x || (vname x == m.2))
  | Rpair _ _ x1 x2 => check_rval m x1 && check_rval m x2
  end.

Definition check_bcmd1 m i := 
  match i with
  | Assgn _ x e => check_rval m x && check_e m e
  | Load  x e   => check_rval m x && check_e m e
  | Store e1 e2 => check_e m e1 && check_e m e2
  end.

Definition vstk (m:map) :=  {|vtype := sword; vname := m.2|}.
Definition estk (m:map) := Pvar (vstk m).
 
Definition check_add (m:map) (p:Z) t (ex:pexpr t) :=
  eqb_pexpr ex (sadd (estk m) (Pconst p)).

Definition check_assgn (m:map) x t (ex:pexpr t) :=
  match Mvar.get m.1 x with
  | None   => false
  | Some p => check_add m p ex
  end.

Definition is_var t (e:pexpr t) := 
  match e with
  | Pvar x => Some x
  | _      => None
  end.

Definition check_set (m:map) t1 (x:var) (e1:pexpr t1) (e e2:pexpr sword) :=
  match e1 with
  | Papp3 _ _ _ _ (Oset _) ex ep e1 =>
    match is_var ex with
    | None    => false
    | Some x' => 
      (x == x') && eqb_pexpr e1 e2 && check_e m e2 && check_e m ep &&
      match Mvar.get m.1 x with
      | None => false
      | Some p => eqb_pexpr e (sadd (estk m) (sadd ep (Pconst p)))
      end
    end
  | _ => false
  end.

Definition check_bcmd2 m i1 i2 :=
  match i1, i2 with
  | Assgn _ (Rvar x) e1, Store ex e2 =>
    (eqb_pexpr e1 e2 && check_e m e1 && check_assgn m x ex) ||
    check_set m x e1 ex e2 
  | _, _ => false
  end.

Definition check_bcmd m i1 i2 := 
  (check_bcmd1 m i1 && eqb_bcmd i1 i2) || check_bcmd2 m i1 i2.

Fixpoint check_i m i1 i2 := 
  match i1, i2 with
  | Cbcmd i1, Cbcmd i2 => check_bcmd m i1 i2
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    eqb_pexpr e1 e2 && check_e m e1 &&
    all2 (check_i m) c11 c21 && all2 (check_i m) c12 c22  
  | Cwhile e1 c1, Cwhile e2 c2 =>
    eqb_pexpr e1 e2 && check_e m e1 && all2 (check_i m) c1 c2 
  | _, _ => false
  end.

(* --------------------------------------------------------------------------- *)

Local Open Scope Z_scope.

Definition stk_ok (w:word) (z:Z) := w + z < I64.modulus.

Definition valid_map (m:map) (stk_size:Z) := 
  forall x px, Mvar.get m.1 x = Some px -> 
     exists sx, size_of (vtype x) = Ok unit sx /\
     [/\ 0 <= px, px + sx <= stk_size &
         forall y py sy, x != y ->  
           Mvar.get m.1 y = Some py -> size_of (vtype y) = Ok unit sy ->
           px + sx <= py \/ py + sy <= px].

Section PROOF.

  Variable m:map.
  Variable stk_size : Z.
  Variable pstk : word.

  Hypothesis pstk_add : stk_ok pstk stk_size.

  Hypothesis validm : valid_map m stk_size.

  Definition valid_stk (vm1:vmap) (m2:mem) pstk :=
    forall x, 
      match Mvar.get m.1 x with
      | Some p =>
        match vtype x with
        | sword => read_mem m2 (I64.repr (pstk + p)) = ok vm1.[{|vtype:=sword;vname := vname x|}]
        | sarr s sword => 
          let t := vm1.[{|vtype := sarr s sword;vname := vname x|}] in
          forall x, (0 <= x < Zpos s)%Z ->
            read_mem m2 (I64.repr (pstk + (x + p))) = ok (FArray.get t (I64.repr x))
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
        (evm s2).[{|vtype:= sword; vname := m.2|}] = pstk /\
        valid_stk (evm s1) (emem s2) pstk ].

  Lemma check_eP t (e:pexpr t) (vm1 vm2:vmap) :
    eq_vm vm1 vm2 -> check_e m e ->
    sem_pexpr vm1 e = sem_pexpr vm2 e.
  Proof.
    move=> Hvm;elim:e => /=
     [x Hx|z _ |b _ |?? o e1 He1|??? o e1 He1 e2 He2|???? o e1 He1 e2 He2 e3 He3] //.
    + (rewrite (Hvm x) //;apply: contra Hx)=> [->|/eqP ->] //=.
      by rewrite eq_refl orbT.
    + by move=> /He1 ->.
    + by move=> /andP[] /He1 -> /He2 ->.
    by move=> /andP[]/andP[]/He1 -> /He2 -> /He3 ->.
  Qed.

  Lemma check_rvalP t (x:rval t) v (vm1 vm2:vmap) :
    check_rval m x -> 
    eq_vm vm1 vm2 -> eq_vm (write_rval vm1 x v) (write_rval vm2 x v).
  Proof.
    elim: x v vm1 vm2 => [x | ?? x1 Hx1 x2 Hx2] /= v vm1 vm2.
    + move=> Hx Heq y Hy1 Hy2.
      case: (x =P y) => [<-|/eqP ?];first by rewrite !Fv.setP_eq.
      by rewrite !Fv.setP_neq //;apply Heq.
    by move=> /andP[] H1 H2 Heq;apply Hx1 => //;apply Hx2.
  Qed.

  Lemma check_rval_in p t (x:rval t) z vm v: 
    Mvar.get m.1 z = Some p ->
    check_rval m x ->
    (write_rval vm x v).[z] = vm.[z].
  Proof.
    move=> Hget;elim : x vm v => [x | ?? x1 Hx1 x2 Hx2] vm v /=.
    + move=> Hx;rewrite Fv.setP_neq //;apply: contra Hx => /eqP ->.
      by rewrite /is_in_stk Hget.
    by move=> /andP[] H1 H2; rewrite Hx1 // Hx2.
  Qed.
    
  Lemma valid_write_rval s1 s2 t (x:rval t) v: 
    check_rval m x -> valid s1 s2 ->
    valid {| emem := emem s1; evm := write_rval (evm s1) x v |}
          {| emem := emem s2; evm := write_rval (evm s2) x v |}.
  Proof.
    move=> Hc [H0 H1 HH H2 [H3 H4]];split => //=.
    + by apply: check_rvalP Hc H2.
    split.    
    + elim: x Hc v (evm s2) H3 => /= [x Hx |?? x1 Hx1 x2 Hx2 /andP[] ??] v vm2;
       last by auto.
      rewrite Fv.setP_neq //;apply: contra Hx => /eqP -> /=.
      by rewrite eq_refl orbC.  
    move=> z;have := H4 z.
    case Heq: Mvar.get => [p|]//.
    case Heqt : vtype => [||| n t1]//=. 
    + by rewrite (@check_rval_in p) //;case: (z) Heqt Heq => ??/= ->.
    case:t1 Heqt=> // Heqt; rewrite (@check_rval_in p) //.
    by case: (z) Heqt Heq => ??/= ->.
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
      + by subst;apply /readV;exists v2; rewrite Hr memory.writeP Hv1 eq_refl.
      by apply /readV;exists w'; rewrite Hr memory.writeP (negbTE Heq) Hv1.
    move=> Hm1;symmetry;apply /readV => -[w'].
    rewrite Hr memory.writeP Hv1;case:ifP => /eqP Heq.
    + by subst;move: Hv1;rewrite Hw.
    by move=> ?;apply Hm1;exists w'.
  Qed.   

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
    case Heqt : vtype => [||| n t1]//=. 
    + rewrite (read_write_mem _ Hm2') memory.writeP.
      have -> : valid_addr (emem s2) v1.
      + by apply /(writeV (emem s2) v1 v2);exists m2'.
      case: eqP=> //= ?;subst v1;have [sz]:= validm Heq.
      rewrite Heqt /= => -[] [] ?;subst sz=> -[] ?? H.
      have := H0 _ H1v1;rewrite I64.unsigned_repr=> [[]|];first by omega.
      by rewrite /I64.max_unsigned; omega.
    case:t1 Heqt=> // Heqt H4' x Hx; have := H4' _ Hx.
    rewrite (read_write_mem _ Hm2') memory.writeP.
    have -> : valid_addr (emem s2) v1.
    + by apply /(writeV (emem s2) v1 v2);exists m2'.
    case:eqP => // H;subst v1;have [sz]:= validm Heq.
    rewrite Heqt /= => -[] [] ?;subst sz=> -[] ?? H.
    have := H0 _ H1v1;rewrite I64.unsigned_repr=> [[]|];first by omega.
    by rewrite /I64.max_unsigned; omega.
  Qed.

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
    Mvar.get m.1 {| vtype := sarr n sword; vname := x |} = Some p ->
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
    have := H4 {| vtype := sword; vname := x |};rewrite Hget /= => H.
    apply /readV;eexists;eauto.
  Qed.

  Lemma get_valid_arr x n p p1 m1 m2: 
     valid m1 m2 -> 
     Mvar.get m.1 {| vtype := sarr n sword; vname := x |} = Some p -> 
     0 <= p1 < Zpos n ->
     valid_addr (emem m2) (I64.repr (pstk + (p1 + p))).
  Proof.
    move=> [] H0 H1 _ H2 [H3 H4] Hget Hp1.
    have := H4 {| vtype := sarr n sword; vname := x |};rewrite Hget /= => /(_ _ Hp1) H.
    apply /readV;eexists;eauto.
  Qed.

  Lemma is_varP t (e:pexpr t) x : 
     is_var e = Some x -> t = vtype x /\ JMeq e (Pvar x).
  Proof. by case: e => //= ? [] ->. Qed.

  Lemma check_setP x t1 (e1:pexpr t1) e e2 :  
    check_set m x e1 e e2 ->
    exists n nx' ep p,
    let x' := {|vtype := sarr n sword; vname := nx'|} in
    [/\ t1 = sarr n sword, x = x', 
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

  Lemma add_repr_r x y : I64.add x (I64.repr y) = I64.repr (x + y).
  Proof.
    by apply: reqP; rewrite !urepr !I64.Z_mod_modulus_eq Zplus_mod_idemp_r eq_refl.
  Qed.

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
      case Heqt: (vtype z)=> [||| n t'] //=.
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
      case: t' Heqt=> //=;case: z Hgetz=> tz z /= Hgetz ?;subst tz=> H p1 Hp1.
      rewrite (read_write_mem (I64.repr (pstk + (p1 + pz))) Hm2') memory.writeP.
      rewrite (H _ Hp1) (get_valid_word Hv Hgetx).
      case: eqP=> // Heqr;last by rewrite Fv.setP_neq.
      have : I64.unsigned (I64.repr (pstk + (p1 + pz))) = I64.repr (pstk + p).
      + by rewrite Heqr.
      rewrite -(get_valid_wrepr Hgetx) -(get_valid_arepr Hgetz) // => ?.
      have [sx /=[][]<-[]??/(_ _ _ _ _ Hgetz (erefl _))]:= validm Hgetx.
      by move=> /(_ isT) ?; omega.
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
    case Heqt: (vtype z)=> [||| n' t'] //=.
    + case: z Heqt Hgetz=> tz z /= -> Hgetz.
      rewrite (read_write_mem _ Hm2') memory.writeP Hvp => ->.
      case: eqP=> // Heqr;last by rewrite Fv.setP_neq.
      have : I64.unsigned (I64.repr (pstk + pz)) = 
                     I64.repr (pstk + (vep + p)).
      + by rewrite -Heqr.
      rewrite -(get_valid_arepr Hgetx)// -(get_valid_wrepr Hgetz) // => ?.
      have [sx /=[][]<-[]??/(_ _ _ _ _ Hgetz (erefl _))]:= validm Hgetx.
      move=> /(_ isT) ?;omega.
    case: t' Heqt=> //=;case: z Hgetz=> tz z /= Hgetz ?;subst tz=> H p1 Hp1.
    rewrite (read_write_mem _ Hm2') memory.writeP Hvp.
    rewrite (H _ Hp1);case: eqP=> // Heqr.
    + have: I64.unsigned (I64.repr (pstk + (p1 + pz))) = 
            I64.repr (pstk + (vep + p)).
      + by rewrite -Heqr.
      rewrite -(get_valid_arepr Hgetx)// -(get_valid_arepr Hgetz)//= => Heq.
      case: (X1 =P  {| vtype := sarr n' sword; vname := z |})=> [[]??|/eqP Hne].
      + subst;rewrite Fv.setP_eq.
        move: Hgetx;rewrite Hgetz => -[] ?; subst pz.
        have -> : p1 = vep by omega.
        by rewrite I64.repr_unsigned FArray.setP_eq.
      have [sx[][]<-[]??/(_ _ _ _ Hne Hgetz (erefl _)) ?]:= validm Hgetx.       
      by omega.
    case: (X1 =P  {| vtype := sarr n' sword; vname := z |})=> [[]??|/eqP Hne];
      last by rewrite Fv.setP_neq.
    subst n' nx';rewrite Fv.setP_eq FArray.setP_neq //.
    apply /negP=> /eqP HH1;have ? : p1 = vep.
    + rewrite HH1 I64.unsigned_repr // /I64.max_unsigned.
      have [sz [][]<-[]?? _]:= validm Hgetz.
      move: pstk_add (I64.unsigned_range pstk);rewrite /stk_ok=> ??. 
      omega.
    by subst p1;apply Heqr;move: Hgetx;rewrite Hgetz=> -[] <-.
  Qed.

  Let Pi (i1:instr) := 
    forall i2, check_i m i1 i2 ->
    forall s1 s1' s2, valid s1 s2 -> sem_i s1 i1 s1' ->
    exists s2', sem_i s2 i2 s2' /\ valid s1' s2'.

  Let Pc (c1:cmd) := 
    forall c2, all2 (check_i m) c1 c2 ->
    forall s1 s1' s2, valid s1 s2 -> sem s1 c1 s1' ->
    exists s2', sem s2 c2 s2' /\ valid s1' s2'.

  Let Pf ta tr (fd:fundef ta tr) := True.

  Let Hskip : Pc [::].
  Proof. 
    move=> [] //= _ s1 s1' s2 Hv H;inversion H;clear H;subst.
    exists s2;split=>//;constructor.
  Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i1 c1 Hi Hc [|i2 c2] //= /andP[] /Hi{Hi}Hi /Hc{Hc}Hc.
    move=> s1 s1' s3 Hv H;inversion H;clear H;subst.
    have [s2' [Hi' Hv2]]:= Hi _ _ _ Hv H3.
    have [s3' [Hc' Hv3]]:= Hc _ _ _ Hv2 H5.
    by exists s3';split=>//; apply: Eseq Hi' Hc'.
  Qed.

  Let Hbcmd : forall bc,  Pi (Cbcmd bc).
  Proof. 
    move=> i1 [] //= i2 Hc s1 s1' s2 Hv H;inversion H;clear H;subst.
    move:Hc;rewrite /check_bcmd => /orP [/andP[] Hc /eqb_bcmdP <-| Hc].
    + have [s2' [H2' Hv']]:= check_bcmd1P Hv Hc H2.
      by exists s2';split=>//;constructor.
    have [s2' [H2' Hv']]:= check_bcmd2P Hv Hc H2.
    by exists s2';split=>//;constructor.
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e1 c11 c12 Hc1 Hc2 [] //= e2 c21 c22.
    move=> /andP[]/andP[]/andP[]/eqb_pexprP [] _ <- He1.
    move=> /Hc1{Hc1}Hc1 /Hc2{Hc2}Hc2 s1 s1' s2 Hv H;inversion H;clear H;subst.
    case: (Hv) H5 => _ _ _ Hvm _;rewrite (check_eP Hvm He1)=> H5.
    case: cond H5 H6 => H5 H6.
    + have [s2' [H6' Hv']]:= Hc1 _ _ _ Hv H6;exists s2';split=>//.
      by apply Eif with true => //.
    have [s2' [H6' Hv']]:= Hc2 _ _ _ Hv H6;exists s2';split=>//.
    by apply Eif with false => //.
  Qed.

  Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Proof. by []. Qed.

  Let Hwhile : forall e c, Pc c -> Pi (Cwhile e c).
  Proof.
    move=> e1 c1 Hc1 [] //= e2 c2.
    move=> /andP[]/andP[] /eqb_pexprP [] _ <- He1 /Hc1{Hc1}Hc1.
    move=> s1 s1' s2 Hv H;inversion H;clear H;subst.
    have : exists s2' : estate,
      sem_while s2 e1 c2 s2' /\ valid s1' s2';last first.
    + by move=> [s2' [Hs Hv']];exists s2';split=> //;constructor.
    elim: H4 He1 Hc1 s2 Hv => {e1 e2 c1 s1 s1'} [s1 e c1|s1 s2 s3 e1 c1].
    + move=> Hse Hce _ s2 Hv;exists s2;split=>//;constructor.
      by case:Hv => _ _ _ Hvm _;rewrite -(check_eP Hvm Hce).
    move=> Hse Hsc Hsw Hrec Hce HH s1' Hv.
    have [s2' [Hs2' Hv2]]:= HH _ _ _ Hv Hsc.
    have [s3' [Hs3' Hv3]]:= Hrec Hce HH _ Hv2.
    case: (Hv) Hse=> _ _ _ Hvm _;rewrite (check_eP Hvm Hce)=> Hse.
    by exists s3';split=> //; apply: EWhileOne Hs3'.
  Qed.

  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof. by []. Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).
  Proof. by []. Qed.

  Lemma check_cP c : Pc c.
  Proof. 
    apply (@cmd_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
  Qed.

End PROOF.

Lemma size_of_pos t s : size_of t = Ok unit s -> 1 <= s.
Proof. case: t=> //= [|p []] //=[] <- //;zify; omega. Qed.

Definition check_fd (nstk:Ident.ident) (sz:Z) (l:list (var * Z)) ta tr 
    (fd: fundef ta tr) (fd': fundef ta tr) :=
  match init_map {|vtype:= sword; vname := nstk|} l sz with 
  | Ok m => 
    (check_rval m (fd_arg fd) && eqb_rval (fd_arg fd) (fd_arg fd')) &&
    (check_e m (rval2pe (fd_res fd)) && eqb_rval (fd_res fd) (fd_res fd')) &&
     all2 (check_i m) (fd_body fd) (fd_body fd')
  | _ => false
  end.

Inductive sem_stk_fd (nstk:Ident.ident) (sz:Z) 
  (sta str : stype) (fd: fundef sta str) 
  (m1:mem) (varg : st2ty sta) (m2:mem) (vres : st2ty str) :=
| SemStkFd : 
    (forall vm0, exists p,
       alloc_stack m1 sz = ok p /\
       exists vm2 m2',
       let vm1 := write_rval vm0 (Rvar {|vtype:= sword; vname:= nstk|}) p.1 in
       let vm1 := write_rval vm1 (fd_arg fd) varg in
       [/\ sem {| emem := p.2; evm := vm1 |} (fd_body fd) {| emem := m2'; evm := vm2 |},
           vres = sem_rval vm2 (fd_res fd) &
           m2 = free_stack m2' p.1 sz]) ->
     sem_stk_fd nstk sz fd m1 varg m2 vres.

Definition init_vm mem pstk (l : seq.seq (var * Z)) vm :=
  let add (vm : vmap) (vp : var * Z) := 
    match vtype vp.1 with
    | sword => 
      let w := Result.default I64.zero (read_mem mem (I64.repr (pstk + vp.2))) in
      vm.[{|vtype := sword; vname := vname vp.1 |} <- w]
    | sarr n sword =>
      let t := fun w => Result.default I64.zero (read_mem mem (I64.repr (pstk + (w + vp.2)))) in
      vm.[{|vtype := sarr n sword; vname := vname vp.1|} <- t]
    | _ => vm 
      end in
  foldl add vm l.

Lemma init_mapP stk pstk l sz m vm m1 m2 :
  alloc_stack m1 sz = ok (pstk, m2) -> 
  init_map stk l sz = Ok unit m -> 
  [/\ valid_map m sz, m.2 = vname stk &
  valid m sz pstk 
    {| emem := m1; evm := init_vm m2 pstk l vm |}
    {| emem := m2; evm := vm.[{|vtype := sword;vname := vname stk|} <- pstk]|}].
Proof.
 (* rewrite /init_map /alloc_stack.  
Toplevel input, characters 21-52:
Anomaly: Uncaught exception Environ.NotEvaluableConst(0). Please report. *)
  move=> /alloc_stackP [Hadd Hread Hval Hbound].
  rewrite /init_map /init_vm.
  set f1 := (f in foldM f _ _ ).
  set f2 := (f in foldl f vm _).
  set g := (g in foldM _ _ _ >>= g). set vstk := vname stk.
  have : forall p p', 
    foldM f1 p l = Ok unit p' -> 
    valid_map (p.1,vstk) p.2 -> 0 <= p.2 ->
    (forall y py sy, Mvar.get p.1 y = Some py ->
        size_of (vtype y) = Ok unit sy -> py + sy <= p.2) ->
    [/\ p.2 <= p'.2, 
        valid_map (p'.1, vstk) p'.2 &
    forall vm1, 
      p'.2 <= sz ->
      valid (p.1,vstk) sz pstk {| emem := m1; evm := vm1 |}
         {| emem := m2; evm := vm.[{| vtype := sword; vname := vstk |} <- pstk] |} ->
      valid (p'.1,vstk) sz pstk {| emem := m1; evm := foldl f2 vm1 l |}
            {| emem := m2; evm := vm.[{| vtype := sword; vname := vstk |} <- pstk] |}].
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
    move=> vm1 Hsz Hvm1.
    rewrite {2}/f2; case Ht : (vtype vp.1) Hs => [|||n []]//=.
    + move=> [] ?;subst svp.
      have := Hval (I64.repr (pstk + vp.2)).
      have -> : (pstk <=? I64.repr (pstk + vp.2)) &&
                  (I64.repr (pstk + vp.2) <? pstk + sz).
      + rewrite I64.unsigned_repr /I64.max_unsigned.
        + by apply /andP;split;[apply /Z.leb_le | apply /Z.ltb_lt];omega.  
        by have ?:= I64.unsigned_range pstk;omega.
      rewrite orbC /= => /readV [w] Hr;rewrite Hr /=;apply Hvm => // {Hvm f1 f2 g}.
      case: Hvm1=> /= W0 W1 W5 W2 [W3 W4];split=> //=.
      + move=> x;rewrite /is_in_stk;rewrite Mvar.setP. 
        case:eqP => // /eqP HH ??;rewrite Fv.setP_neq;first by apply W2.
        by rewrite -Ht;case: (vp.1) HH.
      split=> //.
      move=> x;rewrite Mvar.setP;case:eqP=> [<- | /eqP Hne].
      + by rewrite Ht Fv.setP_eq.
      have /= := W4 x;case: Mvar.get => //= a;case Htx: (vtype x)=> [|||p1 t1]//=.
      + rewrite Fv.setP_neq //.
        by move: Hne;rewrite (var_surj vp.1) (var_surj x) Ht Htx .
      by case:t1 Htx=> Htx //;rewrite Fv.setP_neq.
    move=> [] ?;subst svp. 
    apply Hvm;first by omega.
    case: Hvm1=> /= W0 W1 W5 W2 [W3 W4];split=> //=.
    + move=> x;rewrite /is_in_stk;rewrite Mvar.setP. 
      case:eqP => // /eqP HH ??;rewrite Fv.setP_neq;first by apply W2.
      by rewrite -Ht;case: (vp.1) HH.
      split=>//.
      move=> x;rewrite Mvar.setP;case:eqP=> [<- | /eqP Hne].
      + rewrite Ht /= => w0 Hw0. 
        have := Hval (I64.repr (pstk + (w0 + vp.2))).
        have -> :  (pstk <=? I64.repr (pstk + (w0 + vp.2))) &&
                   (I64.repr (pstk + (w0 + vp.2)) <? pstk + sz).
        + rewrite I64.unsigned_repr.
          apply /andP;split;[apply /Z.leb_le | apply Z.ltb_lt];omega. 
          rewrite /I64.max_unsigned;have ?:= I64.unsigned_range pstk;omega.
      rewrite orbC /= => /readV [w' Hw'];rewrite Hw' /=.
      rewrite Fv.setP_eq /FArray.get.
      have -> : I64.repr (pstk + (I64.repr w0 + vp.2)) = 
                I64.repr (pstk + (w0 + vp.2)).
      + apply: reqP; rewrite !urepr !I64.Z_mod_modulus_eq.
        by rewrite -Zplus_mod_idemp_r Zplus_mod_idemp_l Zplus_mod_idemp_r eq_refl.
      by rewrite Hw'.
    have /= := W4 x;case: Mvar.get => //= a;case Htx: (vtype x)=> [|||p1 []]//=.
    + by rewrite Fv.setP_neq //.
    rewrite Fv.setP_neq //.
    by move: Hne;rewrite (var_surj vp.1) (var_surj x) Ht Htx.
  move=> H;case Heq : foldM => [p'|]//=.
  case: (H _ _ Heq)=> //= Hp' Hv Hvm1.
  rewrite /g;case:ifP => //= /Z.leb_le ? [] <- /=;split=>//.
  + move=> x px Hx.
    case :(Hv x px Hx) => //= sx [] Hsx [] H1 H2 H3.
    by exists sx;split=>//;split=>//;omega.
  apply Hvm1=> //; split=> //=;last by rewrite Fv.setP_eq.
  by move=> x ??;rewrite Fv.setP_neq // eq_sym.
Qed.
 
Lemma check_stk_allocP nstk sz ta tr l (fd:fundef ta tr) fd':
  check_fd nstk sz l fd fd' ->
  forall m1 va m1' vr, 
    sem_call m1 fd va m1' vr ->
    (exists p, alloc_stack m1 sz = ok p) ->
    sem_stk_fd nstk sz fd' m1 va m1' vr.
Proof.
  rewrite /check_fd. 
  case Hinit: init_map => [m|] //=.
  move=> /andP[]/andP[]/andP[] Hcxa /eqb_rvalP[]_ Hexa /andP[] Hcr /eqb_rvalP[]_ Her Hcb.
  move=> m1 va m1' vr H;inversion H;clear H;subst. 
  inversion H0;clear H0;subst=> -[[pstk m2] Halloc].
  constructor => vm0; exists (pstk,m2);split=>//. 
  rewrite -Hexa -Her.
  have [/= Hv Hestk Hval] := init_mapP vm0 Halloc Hinit.
  have [vm2 /= [Hsem Heq]] := H7 (init_vm m2 pstk l vm0).
  pose s2 := {| emem := m2;
                 evm := write_rval vm0.[{| vtype := sword; vname := nstk |} <- pstk]
                           (fd_arg fd) va |}.
  have /= {Hval}Hval := valid_write_rval va Hcxa Hval.
  have [|[m2' vm2'] [Hsem' Hval']]:= check_cP _ Hv Hcb Hval Hsem.
  + by have []:= alloc_stackP Halloc.
  exists vm2', m2';split=> //.
  + case Hval' => _ _ _ H _.
    have := sem_rval2pe (fd_res fd) vm2'.
    by rewrite -(check_eP H Hcr) /= (sem_rval2pe (fd_res fd) vm2) => -[] <-.
  apply eq_memP=> w.
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

