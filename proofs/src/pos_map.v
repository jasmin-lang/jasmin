Require Import ZArith FMapPositive.
From mathcomp Require Import ssreflect eqtype ssrbool choice ssrfun seq.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
Lemma appendA : associative append.
Proof. by elim => //= p Hp y z;rewrite Hp. Qed.

Lemma log_app n p : log_inf (append n p) = (log_inf n + log_inf p)%Z.
Proof. elim: n => /= [ n -> | n -> | ];omega. Qed.

Lemma append_inj n1 n2 p1 p2: log_inf p1 = log_inf p2 -> 
  append n1 p1 = append n2 p2 -> n1 = n2 /\ p1 = p2.
Proof.
  elim: n1 n2 p1 p2 => [ n1 Hn1 | n1 Hn1 | ] [ n2 | n2 | ] //= p1 p2. 
  + by move=> Hl [] /(@Hn1 _ _ _ Hl) []-> ->.
  + move=> Heq Hp2;move: Heq;rewrite -Hp2 /= log_app => ?.
    have ?:= log_inf_correct1 n1;omega.
  + by move=> Hl [] /(@Hn1 _ _ _ Hl) []-> ->.
  + move=> Heq Hp2;move: Heq;rewrite -Hp2 /= log_app => ?.
    have ?:= log_inf_correct1 n1;omega.
  + move=> Heq Hp2;move: Heq;rewrite Hp2 /= log_app => ?.
    have ?:= log_inf_correct1 n2;omega.
  move=> Heq Hp2;move: Heq;rewrite Hp2 /= log_app => ?.
  have ?:= log_inf_correct1 n2;omega.
Qed.

Definition b2P b := 
  if b then 2%positive else 3%positive.

Definition b2P_app b n := 
  if b then xO n else xI n.

Lemma b2P_appP b n : b2P_app b n = append (b2P b) n.
Proof. by case:b. Qed.

Lemma log_b2P_app b n : log_inf (b2P_app b n) = Z.succ (log_inf n).
Proof. by case: b. Qed.

Lemma b2P_app_inj b1 b2 n1 n2 : b2P_app b1 n1 = b2P_app b2 n2 -> b1 = b2 /\ n1 = n2.
Proof. by case: b1 b2 => -[] //= []. Qed.

(* -------------------------------------------------------------------------- *)
Module Type InjPos.

  Parameter t: eqType.

  Parameter t2P : t -> positive.
 
  Axiom t2P_inj : injective t2P.
  
End InjPos.

Module Mmake (K:InjPos).

  Definition t (T:Type) := PositiveMap.t T.

  Definition empty T : t T := PositiveMap.empty T.

  Definition get {T} (m:t T) (k:K.t) := PositiveMap.find (K.t2P k) m. 

  Definition set {T} (m:t T) (k:K.t) (t:T) := PositiveMap.add (K.t2P k) t m.

  Delimit Scope map_scope with ms.
  Local Open Scope map_scope.
  Notation "m .[ s ]" := (get m s): map_scope.
  Reserved Notation "x .[ k <- v ]"
     (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").

  Notation "x .[ k <- v ]" := (set x k v) : map_scope.
  
  Lemma setP {T} m x y (v:T) : m.[x <- v].[y] = if x == y then Some v else m.[y].
  Proof.
    case eqP=> [-> | Hdiff];first by apply PositiveMap.gss.
    by apply PositiveMap.gso=> /K.t2P_inj /esym.
  Qed.

  Lemma setP_eq {T} m x (v:T) : m.[x <- v].[x] = Some v.
  Proof. by rewrite setP eq_refl. Qed.

  Lemma setP_neq {T} m x y (v:T) : x <> y -> m.[x <- v].[y] = m.[y].
  Proof. by rewrite setP=> /eqP /negPf ->. Qed.

End Mmake.

Module Type DInjPos.

  Parameter t: eqType.

  Parameter t2P : t -> positive.
 
  Axiom t2P_inj : injective t2P.
  
  Parameter eq_dec : forall (t1 t2:t), {t1 = t2} + {True}.

  Axiom eq_dec_r : forall t1 t2 tt, eq_dec t1 t2 = right tt -> t1 <> t2.

End DInjPos.

Module DMmake (K:DInjPos).

  Record boxed (P:K.t -> Type) := Box {
    box_t : K.t;
    box_v : P box_t;
  }.

  Definition from_boxed {P} (k:K.t) (b:option (boxed P)) : option (P k):= 
    match b with
    | Some (Box k' v) =>
      match K.eq_dec k' k with
      | left Heq => Some (eq_rect k' P v k Heq)
      | _        => None
      end
    | _ => None
    end.

  Definition t (P:K.t -> Type) := PositiveMap.t (boxed P).

  Definition empty P : t P := PositiveMap.empty (boxed P).

  Definition get {P} (m:t P) (k:K.t) := 
    from_boxed k (PositiveMap.find (K.t2P k) m). 

  Definition set {P} (m:t P) (k:K.t) (v:P k) := 
    PositiveMap.add (K.t2P k) (Box v) m.

  Delimit Scope dmap_scope with dms.
  Local Open Scope dmap_scope.
  Notation "m .[ s ]" := (get m s): dmap_scope.
  Reserved Notation "x .[ k <- v ]"
     (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").

  Notation "x .[ k <- v ]" := (@set _ x k v) : dmap_scope.
  
  Lemma setP {P} (m: t P) x y (v:P x) :
    m.[x <- v].[y] = 
    match K.eq_dec x y with
    | left Heq => Some (eq_rect x P v y Heq)
    | _        => m.[y]
    end.
  Proof.  
    rewrite /set /get /from_boxed /=.
    case H: (K.eq_dec x y) (@K.eq_dec_r x y) => [Heq | []] => [ _ | Hneq].
    + by move:(Heq) H;rewrite -Heq=>{Heq}Heq H;rewrite PositiveMap.gss H.
    have {Hneq} Hneq := Hneq I (erefl _).                                   
    rewrite PositiveMap.gso //. 
    by move=> /K.t2P_inj /esym ?;apply Hneq.
  Qed.

  Lemma setP_eq {T} m x (v:T) : m.[x <- v].[x] = Some v.
  Proof. 
    rewrite setP;case: (K.eq_dec x x) (@K.eq_dec_r x x) => [eq _ | [] ].
    + by rewrite (eq_irrelevance eq (erefl x)).
    by move=> H;elim (H I).
  Qed.

  Lemma setP_neq {T} m x y (v:T) : x <> y -> m.[x <- v].[y] = m.[y].
  Proof. by rewrite setP;case: K.eq_dec. Qed.

End DMmake.



   

                                       
                                    

