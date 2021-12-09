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

From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Utf8.
Require Import compiler_util expr low_memory.

(* -------------------------------------------------------------------- *)

Section WITH_POINTER_DATA.

Context {pd:PointerData}.

(* disp + base + scale * offset *)
Record lea := MkLea {
  lea_disp   : pointer;
  lea_base   : option var_i;
  lea_scale  : pointer;
  lea_offset : option var_i;
}.

Definition lea_const z := MkLea z None 1%R None.

Definition lea_var x := MkLea 0%R (Some x) 1%R None.

Definition mkLea d b sc o :=
  if sc == 0%R then MkLea d b 1%R None
  else MkLea d b sc o.

Definition lea_mul l1 l2 :=
  let 'MkLea d1 b1 sc1 o1 := l1 in
  let 'MkLea d2 b2 sc2 o2 := l2 in
  let d := (d1 * d2)%R in
  match b1, o1, b2, o2 with
  | None  , None  , None  , None   => Some (lea_const d)
  | Some _, None  , None  , None   => Some (mkLea d None d2 b1)
  | None  , None  , Some _, None   => Some (mkLea d None d1 b2)
  | None  , Some _, None  , None   => Some (mkLea d None (d2 * sc1) o1)
  | None  , None  , None  , Some _ => Some (mkLea d None (d1 * sc2) o2)
  | _     , _     , _     , _      => None
  end%R.

Definition lea_add l1 l2 :=
  let 'MkLea d1 b1 sc1 o1 := l1 in
  let 'MkLea d2 b2 sc2 o2 := l2 in
  let disp := (d1 + d2)%R in
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
  end%R.

Definition lea_sub l1 l2 :=
  let 'MkLea d1 b1 sc1 o1 := l1 in
  let 'MkLea d2 b2 sc2 o2 := l2 in
  let disp := (d1 - d2)%R in
  match b2, o2 with
  | None, None => Some (mkLea disp b1 sc1 o1)
  | _   , _    => None
  end.

Fixpoint mk_lea_rec (sz:wsize) e :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) => 
      Some (lea_const (sign_extend Uptr (wrepr sz' z)))
  | Pvar  x          => 
    if is_lvar x then Some (lea_var x.(gv))
    else None
  | Papp2 (Omul (Op_w sz')) e1 e2 =>
    match mk_lea_rec sz e1, mk_lea_rec sz e2 with
    | Some l1, Some l2 => lea_mul l1 l2
    | _      , _       => None
    end
  | Papp2 (Oadd (Op_w sz')) e1 e2 =>
    match mk_lea_rec sz e1, mk_lea_rec sz e2 with
    | Some l1, Some l2 => lea_add l1 l2
    | _      , _       => None
    end
  | Papp2 (Osub (Op_w sz')) e1 e2 =>
    match mk_lea_rec sz e1, mk_lea_rec sz e2 with
    | Some l1, Some l2 => lea_sub l1 l2
    | _      , _       => None
    end
  | _ => None
  end.

Fixpoint push_cast_sz sz e := 
  match e with
  | Papp2 (Oadd Op_int) e1 e2 => 
    Papp2 (Oadd (Op_w sz)) (push_cast_sz sz e1) (push_cast_sz sz e2)

  | Papp2 (Omul Op_int) e1 e2 => 
    Papp2 (Omul (Op_w sz)) (push_cast_sz sz e1) (push_cast_sz sz e2)

  | Papp2 (Osub Op_int) e1 e2 => 
    Papp2 (Osub (Op_w sz)) (push_cast_sz sz e1) (push_cast_sz sz e2)

(*  | Papp1 (Oneg Op_int) e1 =>
    Papp1 (Oneg (Op_w sz)) (push_cast_sz sz e1) *)
  
  | Papp1 (Oint_of_word sz') e1 => 
    if (sz <= sz')%CMP then e1
    else Papp1 (Oword_of_int sz) e 
  | _ => Papp1 (Oword_of_int sz) e
  end.

Fixpoint push_cast e :=
  match e with
  | Papp1 (Oword_of_int sz) e1 => push_cast_sz sz (push_cast e1)
  | Papp1 o e1                 => Papp1 o (push_cast e1)
  | Papp2 o e1 e2              => Papp2 o (push_cast e1) (push_cast e2)
  | _                          => e
  end.

Definition mk_lea sz e := mk_lea_rec sz (push_cast e).

End WITH_POINTER_DATA.
