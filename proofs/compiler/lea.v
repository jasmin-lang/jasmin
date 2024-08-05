From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.
Require Import Utf8.
Require Import expr.
Require Import fexpr.

(* -------------------------------------------------------------------- *)

(* disp + base + scale * offset *)
Record lea := MkLea {
  lea_disp   : Z;
  lea_base   : option var_i;
  lea_scale  : Z;
  lea_offset : option var_i;
}.

Definition lea_const z := MkLea z None 1%Z None.

Definition lea_var x := MkLea 0%Z (Some x) 1%Z None.

Definition mkLea d b sc o :=
  if sc == 0%Z then MkLea d b 1%Z None
  else MkLea d b sc o.

Definition lea_mul l1 l2 :=
  let 'MkLea d1 b1 sc1 o1 := l1 in
  let 'MkLea d2 b2 sc2 o2 := l2 in
  let d := (d1 * d2)%Z in
  match b1, o1, b2, o2 with
  | None  , None  , None  , None   => Some (lea_const d)
  | Some _, None  , None  , None   => Some (mkLea d None d2 b1)
  | None  , None  , Some _, None   => Some (mkLea d None d1 b2)
  | None  , Some _, None  , None   => Some (mkLea d None (d2 * sc1) o1)
  | None  , None  , None  , Some _ => Some (mkLea d None (d1 * sc2) o2)
  | _     , _     , _     , _      => None
  end%Z.

Definition lea_add l1 l2 :=
  let 'MkLea d1 b1 sc1 o1 := l1 in
  let 'MkLea d2 b2 sc2 o2 := l2 in
  let disp := (d1 + d2)%Z in
  match b1, o1    , b2    , o2    with
  | None  , None  , _     , _      => Some (mkLea disp b2 sc2 o2)
  | _     , _     , None  , None   => Some (mkLea disp b1 sc1 o1)
  | Some _, None  , _     , None   => Some (mkLea disp b1 1 b2)
  | Some _, None  , None  , Some _ => Some (mkLea disp b1 sc2 o2)
  | None  , Some _, Some _, None   => Some (mkLea disp b2 sc1 o1)
  | None  , Some _, None  , Some _ =>
    if sc1 == 1 then Some (mkLea disp o1 sc2 o2)
    else if sc2 == 1 then Some (mkLea disp o2 sc1 o1)
    else None
  | _     , _     , _     , _      => None
  end%Z.

Definition lea_sub l1 l2 :=
  let 'MkLea d1 b1 sc1 o1 := l1 in
  let 'MkLea d2 b2 sc2 o2 := l2 in
  let disp := (d1 - d2)%Z in
  match b2, o2 with
  | None, None => Some (mkLea disp b1 sc1 o1)
  | _   , _    => None
  end.

Fixpoint mk_lea_rec (sz: wsize) e :=
  match e with
  | Fapp1 (Oword_of_int sz') (Fconst z) =>
      Some (lea_const (wunsigned (wrepr sz' z)))
  | Fvar  x          => Some (lea_var x)
  | Fapp2 (Omul (Op_w sz')) e1 e2 =>
    match mk_lea_rec sz e1, mk_lea_rec sz e2 with
    | Some l1, Some l2 => lea_mul l1 l2
    | _      , _       => None
    end
  | Fapp2 (Oadd (Op_w sz')) e1 e2 =>
    match mk_lea_rec sz e1, mk_lea_rec sz e2 with
    | Some l1, Some l2 => lea_add l1 l2
    | _      , _       => None
    end
  | Fapp2 (Osub (Op_w sz')) e1 e2 =>
    match mk_lea_rec sz e1, mk_lea_rec sz e2 with
    | Some l1, Some l2 => lea_sub l1 l2
    | _      , _       => None
    end
  | _ => None
  end.

Definition mk_lea sz e :=
  obind (mk_lea_rec sz) (fexpr_of_pexpr e).
