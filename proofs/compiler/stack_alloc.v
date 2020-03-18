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
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils gen_map type var expr low_memory sem.
Require Import constant_prop compiler_util allocation.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Definition cerror {A} msg := 
  @cerror (Cerr_stk_alloc msg) A.

Variant mem_space := 
  | MSglob 
  | MSstack.

Scheme Equality for mem_space. 

Lemma mem_space_axiom : Equality.axiom mem_space_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_mem_space_dec_bl.
  by apply: internal_mem_space_dec_lb.
Qed.

Definition mem_space_eqMixin     := Equality.Mixin mem_space_axiom.
Canonical  mem_space_eqType      := Eval hnf in EqType mem_space mem_space_eqMixin.

Definition mem_space_cmp (ms1 ms2:mem_space) := 
  match ms1, ms2 with
  | MSglob, MSglob => Eq
  | MSglob, MSstack => Lt
  | MSstack, MSglob => Gt
  | MSstack, MSstack => Eq
  end.

Instance mem_spaceO : Cmp mem_space_cmp.
Proof.
  constructor.
  + by case;case.
  + by case;case;case => //= ? [].
  by case;case.
Qed.

Record mem_pos := 
  { mp_s : mem_space;             (* where is stored the data, stack or global *)
    mp_ofs : Z;                   (* the offset *)
  }.

Definition mem_pos_beq (mp1 mp2:mem_pos) := 
  (mp1.(mp_s) == mp2.(mp_s)) && (mp1.(mp_ofs) == mp2.(mp_ofs)).

Lemma mem_pos_axiom : Equality.axiom mem_pos_beq.
Proof.
  rewrite /mem_pos_beq => -[xs1 xo1] [xs2 xo2].
  apply:(iffP idP) => [/andP /= [] /eqP-> /eqP-> //| [-> -> /=]].
  by rewrite !eq_refl.
Qed.

Definition mem_pos_eqMixin     := Equality.Mixin mem_pos_axiom.
Canonical  mem_pos_eqType      := Eval hnf in EqType mem_pos mem_pos_eqMixin.

Module  CmpMp.

  Definition t := [eqType of mem_pos].

  Definition cmp (mp1 mp2: t) := 
    Lex (mem_space_cmp mp1.(mp_s) mp2.(mp_s)) (Z.compare mp1.(mp_ofs) mp2.(mp_ofs)).

  Instance cmpO : Cmp cmp.
  Proof.
    constructor => [x y | y x z c | [mps1 mpo1] [mps2 mpo2]]; rewrite /cmp !Lex_lex.
    + by apply lex_sym => /=; apply cmp_sym.
    + by apply lex_trans=> /=; apply cmp_ctrans.
    by move=> /lex_eq [] /= /(@cmp_eq _ _ mem_spaceO) -> /(@cmp_eq _ _ ZO) ->.
  Qed.

End CmpMp.

Module Mmp :=  Mmake CmpMp.
 
Inductive ptr_kind :=
  | Pstack of Z
  | Pregptr of var 
  | Pstkptr of Z.

Record pos_map := {
  vrip    : var;
  vrsp    : var;
  globals : Mvar.t Z;
  locals  : Mvar.t ptr_kind;
  vnew    : Sv.t;
}.

Module Region.

Record regions := {
  var_region : Mvar.t mem_pos;  (* The region where the value is initialy stored *)
  region_vars : Mmp.t Sv.t;     (* The set of source variables whose value is in the region *)
}.

Definition empty := {|
  var_region   := Mvar.empty _;
  region_vars := Mmp.empty _;
|}.

Definition check_valid (rmap:regions) (x:var) := 
  match Mvar.get rmap.(var_region) x with
  | Some mp =>
    match Mmp.get rmap.(region_vars) mp with
    | Some xs => 
      if Sv.mem x xs then ok mp
      else cerror "invalid variable (check alias)"
    | None => cerror "invalid variable (check alias)"
    end
  | None => cerror "no associated region"
  end.

Definition check (rmap:regions) (x:var) ws := 
  Let mp := check_valid rmap x in
  if is_align (wrepr _ mp.(mp_ofs)) ws then ok tt
  else cerror "unaligned access: please report".

Definition set_word (rmap:regions) (x:var) := 
  match Mvar.get rmap.(var_region) x with
  | Some mp => 
    if mp.(mp_s) == MSglob then cerror "try to write global region"
    else 
      let rv := Mmp.set rmap.(region_vars) mp (Sv.singleton x) in
      ok {| var_region := rmap.(var_region);
            region_vars := rv |}
  | None => cerror "unknown region: please report"
  end.

Definition remove rmap x := 
  match Mvar.get rmap.(var_region) x with
  | None => rmap
  | Some mp => 
    let rv := 
      match Mmp.get rmap.(region_vars) mp with
      | Some xs => Mmp.set rmap.(region_vars) mp (Sv.remove x xs)
      | None    => rmap.(region_vars)
      end in
    {| var_region  := Mvar.remove rmap.(var_region) x;
       region_vars := rv |}
  end.

Definition set rmap x mp := 
  let xs := 
     match Mmp.get rmap.(region_vars) mp with
     | Some xs => xs
     | None    => Sv.empty 
      end in  
  {| var_region  := Mvar.set rmap.(var_region) x mp;
     region_vars := Mmp.set rmap.(region_vars) mp (Sv.add x xs) |}.

Definition rm_set rmap x mp := 
  set (remove rmap x) x mp.

Definition set_move (rmap:regions) (x y:var) := 
  Let mp := check_valid rmap y in
  ok (rm_set rmap x mp).

Definition set_move_glob (rmap:regions) (x:var) (ofs:Z) := 
  let mp := {| mp_s := MSglob; mp_ofs := ofs |} in
  rm_set rmap x mp.

Definition set_init (rmap:regions) x pk := 
  match pk with
  | Pstack z =>
    let mp := {| mp_s := MSstack; mp_ofs := z |} in
    let rmap := remove rmap x in
    set rmap x mp

  | Pstkptr _ => rmap
  | Pregptr _ => rmap
  end.

Definition incl (r1 r2:regions) := 
  Mvar.fold 
    (fun x mp b => b && Mvar.get r2.(var_region) x == Some mp) r1.(var_region) true &&
  Mmp.fold 
    (fun mp xs b => b && match Mmp.get r2.(region_vars) mp with
                         | Some xs' => Sv.subset xs xs'
                         | None => false
                         end) r1.(region_vars) true.

Definition merge (r1 r2:regions) := 
  let vr := r2.(var_region) in
  let rv := r2.(region_vars) in
  {| var_region := 
       Mvar.fold (fun x mp m =>
         match Mvar.get vr x with
         | Some mp' => if mp == mp' then Mvar.set m x mp else m
         | None     => m
         end) r1.(var_region) (Mvar.empty _);
     region_vars := 
       Mmp.fold (fun mp xs m =>
         match Mmp.get rv mp with
         | Some xs' => Mmp.set m mp (Sv.inter xs xs')
         | None     => m
         end) r1.(region_vars) (Mmp.empty _); |}.
  
End Region.

Import Region.
  
Definition cast_w ws := Papp1 (Oword_of_int ws).

Definition cast_ptr := cast_w Uptr.

Definition cast_const z := cast_ptr (Pconst z).

Definition mul := Papp2 (Omul (Op_w Uptr)).
Definition add := Papp2 (Oadd (Op_w Uptr)).

Definition cast_word e := 
  match e with
  | Papp1 (Oint_of_word U64) e1 => e1
  | _  => cast_ptr e
  end.

Definition mk_ofs ws e1 ofs := 
  let sz := mk_scale ws in
  if is_const e1 is Some i then 
    cast_const (i * sz + ofs)%Z
  else 
    add (mul (cast_const sz) (cast_word e1)) (cast_const ofs).

Section Section.

Variables (pmap:pos_map).

Section ALLOC_E.

Variables (rmap: regions).

Definition get_global (x:var) := 
  match Mvar.get pmap.(globals) x with
  | None => cerror "unallocated global variable: please report"
  | Some z => ok z
  end.

Definition get_local (x:var) := Mvar.get pmap.(locals) x.

Definition check_diff (x:var) :=
  if Sv.mem x pmap.(vnew) then cerror "the code write new variables, please report"
  else ok tt.

Definition check_var (x:var) := 
  match get_local x with
  | None => check_diff x
  | _   => cerror "not a reg variable" 
  end.

Definition with_var xi x := 
  {| v_var := x; v_info := xi.(v_info) |}.

Definition mk_addr x ws (pk:ptr_kind) (e1:pexpr) := 
  match pk with
  | Pstack z  => ok (with_var x pmap.(vrsp), mk_ofs ws e1 z)
  | Pregptr p => ok (with_var x p,    mk_ofs ws e1 0)
  | Pstkptr z => cerror "stack pointer in expression" 
  end.
 
Fixpoint alloc_e (e:pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e

  | Pvar   x =>

    let xv := x.(gv) in
    if is_glob x then
      Let z := get_global xv in
      if is_word_type (vtype xv) is Some ws then
        if is_align (wrepr _ z) ws then
          ok (Pload ws (with_var xv pmap.(vrip)) (cast_const z))
        else cerror "not aligned global: please report"
      else cerror "not a word variable in expression" 
    else
      match get_local xv with 
      | None => 
        Let _ := check_diff xv in ok e
      | Some pk => 
        if is_word_type (vtype xv) is Some ws then 
          Let _ := Region.check rmap xv ws in
          Let pofs := mk_addr xv ws pk (Pconst 0) in
          ok (Pload ws pofs.1 pofs.2)
        else cerror "not a word variable in expression" 
      end

  | Pget ws x e1 =>

    Let e1 := alloc_e e1 in
    let xv := x.(gv) in
    if is_glob x then
      Let z := get_global xv in
      if is_const e1 is Some _ then
        if is_align (wrepr _ z) ws then
          let ofs := mk_ofs ws e1 z in 
          ok (Pload ws (with_var xv pmap.(vrip)) ofs)
        else cerror "not aligned global array access: please report"
      else cerror "not constant global array index: use pointer"
    else
      match get_local xv with 
      | None => Let _ := check_diff x.(gv) in ok e 
      | Some pk => 
        Let _ := Region.check rmap xv ws in
        Let pofs := mk_addr xv ws pk e1 in
        ok (Pload ws pofs.1 pofs.2)
      end

  | Pload ws x e1 =>
    Let _ := check_var x in
    Let e1 := alloc_e e1 in
    ok (Pload ws x e1)

  | Papp1 o e1 =>
    Let e1 := alloc_e e1 in
    ok (Papp1 o e1)
   
  | Papp2 o e1 e2 =>
    Let e1 := alloc_e e1 in
    Let e2 := alloc_e e2 in
    ok (Papp2 o e1 e2)

  | PappN o es => 
    Let es := mapM alloc_e es in
    ok (PappN o es)  

  | Pif t e e1 e2 =>
    Let e := alloc_e e in
    Let e1 := alloc_e e1 in
    Let e2 := alloc_e e2 in
    ok (Pif t e e1 e2)
  end.

  Definition alloc_es := mapM alloc_e.
 
End ALLOC_E.

Definition alloc_lval (rmap: regions) (r:lval) ty := 
  match r with
  | Lnone _ _ => ok (rmap, r)

  | Lvar x =>
    match get_local x with 
    | None => Let _ := check_diff x in ok (rmap, r)
    | Some pk => 
      if is_word_type (vtype x) is Some ws then 
        if ty == sword ws then 
          Let pofs := mk_addr x ws pk (Pconst 0) in
          let r := Lmem ws pofs.1 pofs.2 in
          Let rmap := Region.set_word rmap x in
          ok (rmap, r)
        else cerror "invalid type for assignment"
      else cerror "not a word variable in assignment"
    end

  | Laset ws x e1 =>
    Let e1 := alloc_e rmap e1 in
    match get_local x with
    | None => Let _ := check_diff x in ok (rmap, r)
    | Some pk => 
      Let _ := Region.check rmap x ws in
      Let pofs := mk_addr x ws pk e1 in
      let r := Lmem ws pofs.1 pofs.2 in
      Let rmap := Region.set_word rmap x in
      ok (rmap, r)
    end   

  | Lmem ws x e1 =>
    Let _ := check_var x in
    Let e1 := alloc_e rmap e1 in
    ok (rmap, Lmem ws x e1)
  end.

Definition is_Pvar e := 
  match e with
  | Pvar x => Some x 
  | _      => None
  end.

Definition is_var e := 
  match e with
  | Pvar x => if is_lvar x then Some x.(gv) else None
  | _      => None
  end.

Definition is_lv_var lv := 
  match lv with
  | Lvar x => Some x
  | _      => None
  end.

Definition get_e_pointer x (k:option ptr_kind) :=
  match k with
  | None => None
  | Some (Pstack _)  => None
  | Some (Pregptr p) => Some (Pvar (mk_lvar (with_var x p)))
  | Some (Pstkptr z) => Some (Pload Uptr (with_var x pmap.(vrsp)) (cast_const z))
  end.

Definition get_lv_pointer x (k:option ptr_kind) := 
  match k with
  | None => None
  | Some (Pstack _)  => None
  | Some (Pregptr p) => Some (Lvar (with_var x p))
  | Some (Pstkptr z) => Some (Lmem Uptr (with_var x pmap.(vrsp)) (cast_const z))
  end.

Definition is_move_ptr_to_stack (rmap: regions) xk y :=
  match xk with
  | Some (Pstack z) =>
    match check_valid rmap y with
    | Ok mp => 
      if (mp == {| mp_s := MSstack; mp_ofs := z |}) then true
      else false
    | _ => false
    end
  | _ => false
  end.

Definition is_move_ptr_x (rmap: regions) x ty y := 
  match is_lv_var x, is_var y with
  | Some x, Some y =>
    if (ty == x.(vtype)) && (ty == y.(vtype)) then
      let xk := get_local x in
      if is_move_ptr_to_stack rmap xk y then Some((x,y),None)
      else 
        let yk := get_local y in
        match get_lv_pointer x xk, get_e_pointer y yk with
        | Some xpofs, Some ypofs => Some ((x,y), Some(xpofs, ypofs))
        | _, _ => None 
        end
    else None
  | _, _ => None
  end.

Definition is_move_ptr (rmap: regions) (i:instr_r) := 
  match i with
  | Cassgn x _ ty e => is_move_ptr_x rmap x ty e
  | Copn [::x] _ (Ox86 (MOV ws)) [::e] => is_move_ptr_x rmap x (sword ws) e
  | _ => None
  end.

Definition mov_ptr x y :=
  Copn [:: x] AT_none (Ox86 (MOV Uptr)) [::y].

Definition lea_ptr x y ptr ofs := 
  Copn [::x] AT_none (Ox86 (LEA Uptr)) 
       [:: add (Pvar (mk_lvar (with_var y ptr))) (cast_ptr ofs)].

(* x =& y *)
Definition alloc_address rmap r ty e :=
  match is_lv_var r, is_Pvar e with
  | Some x, Some y =>
    if (ty == x.(vtype)) && (ty == y.(gv).(vtype)) then
      let xk := get_local x in
      match get_lv_pointer x xk with 
      | Some xp => 
        if is_glob y then
          let y := y.(gv) in
          Let ofs := get_global y in
          let rmap := Region.set_move_glob rmap x ofs in
          ok (rmap, lea_ptr xp y pmap.(vrip) ofs)
        else 
          let y := y.(gv) in
          match get_local y with
          | Some (Pstack ofs) => 
            Let rmap := Region.set_move rmap x y in
            ok (rmap, lea_ptr xp y pmap.(vrsp) ofs)
          | None => cerror "can compute the address of a register"
          | Some (Pregptr _) => cerror "can compute the address of a reg ptr"
          | Some (Pstkptr z) => cerror "can compute the address of a stack ptr"
          end 
      | None => cerror "cannot compute the address of the destination"
      end
    else cerror "invalid type in =&" 
  | _, _ => cerror "invalid =&"
  end.
  
Definition fmapM {eT aT bT cT} (f : aT -> bT -> result eT (aT * cT))  : aT -> seq bT -> result eT (aT * seq cT) :=
  fix mapM a xs :=
    match xs with
    | [::] => Ok eT (a, [::])
    | [:: x & xs] =>
      Let y := f a x in
      Let ys := mapM y.1 xs in
      Ok eT (ys.1, y.2 :: ys.2)
    end.

Definition fmapM2 {eT aT bT cT dT} (e:eT) (f : aT -> bT -> cT -> result eT (aT * dT)) : 
   aT -> seq bT -> seq cT -> result eT (aT * seq dT) :=
  fix mapM a lb lc :=
    match lb, lc with
    | [::], [::] => Ok eT (a, [::])
    | [:: b & bs], [:: c & cs] =>
      Let y := f a b c in
      Let ys := mapM y.1 bs cs in
      Ok eT (ys.1, y.2 :: ys.2)
    | _, _ => Error e
    end.

Definition bad_lval_number := Cerr_stk_alloc "invalid number of lval".

Definition alloc_lvals rmap rs tys := 
  fmapM2 bad_lval_number alloc_lval rmap rs tys.

Section LOOP.

 Variable ii:instr_info.

 Variable check_c2 : regions -> ciexec ((regions * regions) * (pexpr * (seq instr * seq instr)) ).

 Fixpoint loop2 (n:nat) (m:regions) := 
    match n with
    | O => cierror ii (Cerr_Loop "stack_alloc")
    | S n =>
      Let m' := check_c2 m in
      if incl m m'.1.2 then ok (m'.1.1, m'.2)
      else loop2 n (merge m m'.1.2)
    end.

End LOOP.

(* FIXME: this is durty *)
Definition nop xi :=
  let x := {| v_var := pmap.(vrsp); v_info := xi |} in
  Cassgn (Lvar x) AT_none (sword Uptr) (Pvar (mk_lvar x)).

Fixpoint alloc_i (rmap:regions) (i: instr) : result instr_error (regions * instr) :=
  let (ii, ir) := i in
  Let ir := 
    let mv_sp := is_move_ptr rmap ir in
    match mv_sp with
    | Some ((x,y), mv) =>
      let ir := 
        match mv with
        | Some (xp,yp) => mov_ptr xp yp
        | None         => nop y.(v_info) 
        end in
      Let rmap := add_iinfo ii (Region.set_move rmap x.(v_var) y.(v_var)) in
      ok (rmap, ir)
    | None =>
    match ir with
    | Cassgn r t ty e => 
      if t == AT_address then
        add_iinfo ii (alloc_address rmap r ty e)
      else
        Let e := add_iinfo ii (alloc_e rmap e) in
        Let r := add_iinfo ii (alloc_lval rmap r ty) in
        ok (r.1, Cassgn r.2 t ty e)

    | Copn rs t o e => 
      Let e  := add_iinfo ii (alloc_es rmap e) in
      Let rs := add_iinfo ii (alloc_lvals rmap rs (sopn_tout o)) in
      ok (rs.1, Copn rs.2 t o e)               
  
    | Cif e c1 c2 => 
      Let e := add_iinfo ii (alloc_e rmap e) in
      Let c1 := fmapM alloc_i rmap c1 in
      Let c2 := fmapM alloc_i rmap c2 in
      let rmap:= merge c1.1 c2.1 in
      ok (rmap, Cif e c1.2 c2.2)
  
    | Cwhile a c1 e c2 => 
      let check_c sm := 
        Let c1 := fmapM alloc_i rmap c1 in
        let sm := c1.1 in
        Let e := add_iinfo ii (alloc_e rmap e) in
        Let c2 := fmapM alloc_i rmap c2 in
        ok ((sm, c2.1), (e, (c1.2, c2.2))) in
      Let r := loop2 ii check_c Loop.nb rmap in
      ok (r.1, Cwhile a r.2.2.1 r.2.1 r.2.2.2)
  
    | Cfor _ _ _  => cierror ii (Cerr_stk_alloc "don't deal with for loop")
    | Ccall _ _ _ _ => cierror ii (Cerr_stk_alloc "don't deal with call")
    end end in
  ok (ir.1, MkI ii ir.2).

Definition size_of (t:stype) :=
  match t with
  | sword sz => ok (wsize_size sz)
  | sarr n   => ok (Zpos n)
  | _      => cerror "size_of"
  end.

Definition aligned_for (ty: stype) (ofs: Z) : bool :=
  match ty with
  | sarr _ => true
  | sword sz => is_align (wrepr _ ofs) sz
  | sbool | sint => false
  end.

Definition init_global_map (sz:Z) (l:list (var * Z)) : cexec (Mvar.t Z) :=
  let add (vp:var*Z) (mp:Mvar.t Z * Z) :=
    let '(v, p) := vp in
    if (mp.2 <=? p)%Z then
      let ty := vtype v in
      if aligned_for ty p then
      Let s := size_of ty in
      cok (Mvar.set mp.1 v p, p + s)%Z
    else cerror "not aligned"
    else cerror "overlap" in
  Let mp := foldM add (Mvar.empty Z, 0%Z) l in
  if (mp.2 <=? sz)%Z then cok mp.1
  else cerror "global size".

Definition init_local_map vrip vrsp 
    (sz:Z) (l:list (var * ptr_kind)) : cexec (Mvar.t ptr_kind * regions * Sv.t) :=
  let check_diff x := 
      if (x == vrip) || (x == vrsp) then
        cerror "invalid reg pointer, please report" 
      else ok tt in

  let add_ty x pk ty p (mp:Mvar.t ptr_kind * Z * regions * Sv.t) := 
    let '(lmap, ofs, rmap, sv) := mp in
    if (ofs <=? p)%Z then
      if aligned_for ty p then
        Let s := size_of ty in
        ok (Mvar.set lmap x pk, p + s, Region.set_init rmap x pk, sv)%Z
      else cerror "not aligned"
    else cerror "overlap" in

  let add (vp:var*ptr_kind) (mp:Mvar.t ptr_kind * Z * regions * Sv.t) :=
    let '(v, pk) := vp in
    Let _ := check_diff v in
    match pk with
    | Pstack p  => add_ty v pk (vtype v)    p mp 
    | Pstkptr p => add_ty v pk (sword Uptr) p mp
    | Pregptr x => 
      let '(lmap, ofs, rmap, sv) := mp in
      Let _ := check_diff x in
      if vtype x == sword Uptr then 
        ok (Mvar.set lmap v pk, ofs, Region.set_init rmap x pk, Sv.add x sv)%Z    
      else cerror "invalid pointer type, please report" 
    end in

  let sv := Sv.add vrip (Sv.add vrsp Sv.empty) in
  Let mp := foldM add (Mvar.empty ptr_kind, 0%Z, Region.empty, sv) l in
  let '(lmap, ofs, rmap, sv) := mp in
  if (ofs <=? sz)%Z then ok (lmap, rmap, sv)
  else cerror "stack size, please report".

End Section.

(* TODO : move *)
Definition add_err_fun (A : Type) (f : funname) (r : cexec A) :=
  match r with
  | ok _ a => ok a
  | Error e => Error (Ferr_fun f e)
  end.

(* We start by doing 
   1/ stack allocation
   2/ Reg allocation
   3/ if we have remaining register to save the stack pointer we use on those register 
      else 
        4/ we restart stack allocation and we keep one position in the stack to save the stack pointer 
        5/ Reg allocation
*)
 
Definition with_body eft (fd:_fundef eft) body := {|
  f_iinfo  := fd.(f_iinfo);
  f_tyin   := fd.(f_tyin);
  f_params := fd.(f_params);
  f_body   := body;
  f_tyout  := fd.(f_tyout);
  f_res    := fd.(f_res);
  f_extra  := fd.(f_extra); 
|}.

Definition alloc_fd_aux
   vrip vrsp mglob  
   (stk_alloc_fd : ufun_decl -> bool -> (Z * list (var * ptr_kind) * Z))
   (reg_alloc_fd : bool -> funname -> ufundef -> ufundef * list var * option var)
   (save_stack : bool)
   (f: ufun_decl) :=
  match f return result fun_error (option (ufundef * ufundef * stk_fun_extra)) with
  | (fn, fd) => 
    let '(sz, sfd, stk_pos) := stk_alloc_fd f save_stack in
    Let mstk := add_err_fun fn (init_local_map vrip vrsp sz sfd) in
    let '(lmap, rmap, sv) := mstk in
    let pmap := {| 
      vrip    := vrip;
      vrsp    := vrsp;
      globals := mglob; 
      locals  := lmap;
      vnew    := sv;
    |} in
    Let body := add_finfo fn fn (fmapM (alloc_i pmap) rmap fd.(f_body)) in
    Let _ := add_err_fun fn (mapM (fun (x:var_i) => check_var pmap x) fd.(f_res)) in
    let fd1 := with_body fd body.2 in
    let '(fd2, to_save, oreg) := reg_alloc_fd (sz == 0) fn fd1 in
    if sz == 0 then 
      let f_extra := {| sf_stk_sz := sz; sf_extra := (to_save, SavedStackNone) |} in
      ok (Some (fd1, fd2, f_extra))
    else match oreg with
    | Some r => 
      let f_extra := {| sf_stk_sz := sz; sf_extra := (to_save, SavedStackReg r) |} in
      ok (Some (fd1, fd2, f_extra))
    | None => 
      if save_stack then 
        let f_extra := {| sf_stk_sz := sz; sf_extra := (to_save, SavedStackStk stk_pos) |} in
        ok (Some(fd1, fd2, f_extra)) 
      else ok None
    end
  end.

Definition swith_extra (fd:ufundef) f_extra : sfundef := {|
  f_iinfo  := fd.(f_iinfo);
  f_tyin   := fd.(f_tyin);
  f_params := fd.(f_params);
  f_body   := fd.(f_body);
  f_tyout  := fd.(f_tyout);
  f_res    := fd.(f_res);
  f_extra  := f_extra; 
|}.


Definition check_reg_alloc p_extra fn (fd1 fd2:ufundef) f_extra := 
  let fd1 := swith_extra fd1 f_extra in
  let fd2 := swith_extra fd2 f_extra in
  Let _ := CheckAllocRegS.check_fundef p_extra p_extra (fn,fd1) (fn, fd2) tt in
  ok (fn, fd2).

Definition alloc_fd p_extra mglob 
    stk_alloc_fd 
    (reg_alloc_fd : bool -> funname -> ufundef -> ufundef * list var * option var)
    (f: ufun_decl) :=
  let vrip := {| vtype := sword Uptr; vname := p_extra.(sp_rip) |} in
  let vrsp := {| vtype := sword Uptr; vname := p_extra.(sp_stk_id) |} in
  Let info := alloc_fd_aux vrip vrsp mglob stk_alloc_fd reg_alloc_fd false f in
  match info with
  | Some (fd1, fd2, f_extra) => check_reg_alloc p_extra f.1 fd1 fd2 f_extra 
  | None =>
    Let info := alloc_fd_aux vrip vrsp mglob stk_alloc_fd reg_alloc_fd true f in
    match info with
    | Some (fd1, fd2, f_extra) => check_reg_alloc p_extra f.1 fd1 fd2 f_extra 
              (* FIXME: error msg *)
    | None => Error (Ferr_msg (Cerr_linear "alloc_fd: assert false"))
    end
  end.    
  
Definition check_glob (m: Mvar.t Z) (data:seq u8) (gd:glob_decl) := 
  let x := gd.1 in
  match Mvar.get m x with
  | None => false 
  | Some z =>
    let n := Z.to_nat z in
    let data := drop n data in
    match gd.2 with
    | @Gword ws w =>
      let s := Z.to_nat (wsize_size ws) in 
      (s <= size data) && 
      (LE.decode ws (take s data) == w)
    | @Garr p t =>
      let s := Z.to_nat p in
      (s <= size data) &&
      all (fun i => 
             match WArray.get U8 t (Z.of_nat i) with
             | Ok w => nth 0%R data i == w
             | _    => false
             end) (iota 0 s)
    end
  end.

Definition check_globs (gd:glob_decls) (m:Mvar.t Z) (data:seq u8) := 
  all (check_glob m data) gd.

Definition init_map (sz:Z) (l:list (var * Z)) : cexec (Mvar.t Z) :=
  let add (vp:var*Z) (mp:Mvar.t Z * Z) :=
      let '(v, p) := vp in
    if (mp.2 <=? p)%Z then
      let ty := vtype v in
      if aligned_for ty vp.2 then
      Let s := size_of ty in
      cok (Mvar.set mp.1 v p, p + s)%Z
    else cerror "not aligned"
    else cerror "overlap" in
  Let mp := foldM add (Mvar.empty Z, 0%Z) l in
  if (mp.2 <=? sz)%Z then cok mp.1
  else cerror "global size".

Definition alloc_prog nrsp stk_alloc_fd reg_alloc_fd 
      (glob_alloc_p : uprog -> seq u8 * Ident.ident * list (var * Z) ) P := 
  let: ((data, rip), l) := glob_alloc_p P in 
  Let mglob := add_err_msg (init_map (Z.of_nat (size data)) l) in
  let p_extra :=  {| 
    sp_rip   := rip; 
    sp_globs := data; 
    sp_stk_id := nrsp;
  |} in
  if rip == nrsp then Error (Ferr_msg (Cerr_stk_alloc "rip and rsp clash, please report"))
  else if check_globs P.(p_globs) mglob data then
    Let p_funs := mapM (alloc_fd p_extra mglob stk_alloc_fd reg_alloc_fd) P.(p_funcs) in
    ok  {| p_funcs  := p_funs;
           p_globs := [::];
           p_extra := p_extra;
        |}
  else 
     Error (Ferr_msg (Cerr_stk_alloc "invalid data: please report")).
