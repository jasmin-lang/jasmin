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

Local
Definition cerror {A} msg :=
  @cerror (Cerr_stk_alloc msg) A.

Local
Definition cferror {A} fn msg :=
  @Error _ A (Ferr_fun fn (Cerr_stk_alloc msg)).

Definition mem_space := var.

Record mem_pos := 
  { mp_s : var;                   (* where is stored the data, stack or global *)
    mp_ofs : Z;                   (* the offset                                *) 
    mp_align : wsize;             (* the alignment of the corresponding region *)
    mp_writable : bool;           (* the region is writable or not             *)
  }.

Definition mem_pos_beq (mp1 mp2:mem_pos) := 
  [&& mp1.(mp_s)        == mp2.(mp_s), 
      mp1.(mp_ofs)      == mp2.(mp_ofs),
      mp1.(mp_align)    == mp2.(mp_align) &
      mp1.(mp_writable) == mp2.(mp_writable)].

Definition mem_pos_same (mp1 mp2:mem_pos) := 
  (mp1.(mp_s) == mp2.(mp_s)) && (mp1.(mp_ofs) == mp2.(mp_ofs)).

Lemma mem_pos_axiom : Equality.axiom mem_pos_beq.
Proof.
  rewrite /mem_pos_beq => -[xs1 xo1 xa1 xw1] [xs2 xo2 xa2 xw2].
  by apply:(iffP and4P) => /= [[/eqP -> /eqP -> /eqP -> /eqP ->] | [-> -> -> ->]].
Qed.

Definition mem_pos_eqMixin     := Equality.Mixin mem_pos_axiom.
Canonical  mem_pos_eqType      := Eval hnf in EqType mem_pos mem_pos_eqMixin.

Module CmpMp.

  Definition t := [eqType of mem_pos].

  Definition cmp (mp1 mp2: t) := 
    Lex (bool_cmp mp1.(mp_writable) mp2.(mp_writable))
     (Lex (wsize_cmp mp1.(mp_align) mp2.(mp_align))
       (Lex (var_cmp mp1.(mp_s) mp2.(mp_s)) (Z.compare mp1.(mp_ofs) mp2.(mp_ofs)))).

  Instance cmpO : Cmp cmp.
  Proof.
    constructor => [x y | y x z c | [????] [????]]; rewrite /cmp !Lex_lex.
    + by repeat (apply lex_sym; first by apply cmp_sym); apply cmp_sym.
    + by repeat (apply lex_trans=> /=; first by apply cmp_ctrans); apply cmp_ctrans.
    move=> /lex_eq [] /= h1 /lex_eq [] /= h2 /lex_eq [] /= h3 h4.
    by rewrite (cmp_eq h1) (cmp_eq h2) (cmp_eq h3) (cmp_eq h4).
  Qed.

End CmpMp.

Module Mmp :=  Mmake CmpMp.

Inductive ptr_kind :=
  | Pstack  `(Z) `(wsize)
  | Pregptr `(var)
  | Pstkptr `(Z).

Record param_info := { 
  pp_ptr      : var;
  pp_writable : bool;
  pp_align    : wsize;
}.

Record pos_map := {
  vrip    : var;
  vrsp    : var;
  globals : Mvar.t (Z * wsize);
  locals  : Mvar.t ptr_kind;
  vnew    : Sv.t;
}.

Definition check_align mp ws :=
  assert (ws <= mp.(mp_align))%CMP
    (Cerr_stk_alloc "unaligned offset").

Definition writable mp := 
  assert mp.(mp_writable)
   (Cerr_stk_alloc "Cannot write a constant pointer").

Definition mp_stack rsp ofs align := 
  {| mp_s := rsp; mp_ofs := ofs; mp_align := align; mp_writable := true |}.

Definition mp_glob rip ofs_align := 
  {| mp_s := rip; mp_ofs := ofs_align.1; mp_align := ofs_align.2; mp_writable := false |}.

Module Region.

Record regions := {
  var_region : Mvar.t mem_pos;  (* The region where the value is initialy stored            *)
  region_vars : Mmp.t Sv.t;     (* The set of source variables whose value is in the region *)
}.

Definition empty := {|
  var_region   := Mvar.empty _;
  region_vars := Mmp.empty _;
|}.

Definition check_valid (rmap:regions) (x:var) := 
  match Mvar.get rmap.(var_region) x with
  | Some mp =>
    Let _ := 
      match Mmp.get rmap.(region_vars) mp with
      | Some xs => 
        if Sv.mem x xs then ok tt
        else cerror "invalid variable (check alias)"
      | None => cerror "invalid variable (check alias)"
      end in
    ok mp
  | None => cerror "no associated region"
  end.

Definition remove rmap mp := 
  {| var_region  := rmap.(var_region);
     region_vars := Mmp.remove rmap.(region_vars) mp |}.

Definition rset_word rmap x mp :=
   {| var_region  := Mvar.set rmap.(var_region) x mp;
      region_vars := Mmp.set rmap.(region_vars) mp (Sv.singleton x) |}.

Definition set_word (rmap:regions) (x:var) ws mp := 
  Let _ := writable mp in
  Let _ := check_align mp ws in
  ok (rset_word rmap x mp).

Definition set rmap x mp := 
  let xs := odflt Sv.empty (Mmp.get rmap.(region_vars) mp) in
  {| var_region  := Mvar.set rmap.(var_region) x mp;
     region_vars := Mmp.set rmap.(region_vars) mp (Sv.add x xs) |}.

Definition set_move (rmap:regions) (x y:var) := 
  Let mp := check_valid rmap y in
  ok (set rmap x mp).

Definition set_init rsp (rmap:regions) x pk := 
  match pk with
  | Pstack ofs align => set rmap x (mp_stack rsp ofs align)
  | Pstkptr _ => rmap
  | Pregptr _ => rmap
  end.

Definition incl (r1 r2:regions) := 
  Mvar.incl (fun x mp1 mp2 => mp1 == mp2) r1.(var_region) r2.(var_region) &&
  Mmp.incl (fun x xs1 xs2 => Sv.subset xs1 xs2) r1.(region_vars) r2.(region_vars).

Definition merge (r1 r2:regions) := 
  let vr := r2.(var_region) in
  let rv := r2.(region_vars) in
  {| var_region := 
       Mvar.map2 (fun _ omp1 omp2 =>
        match omp1, omp2 with
        | Some mp1, Some mp2 => if mp1 == mp2 then omp1 else None
        | _, _ => None
        end) r1.(var_region) r2.(var_region);
     region_vars := 
       Mmp.map2 (fun _ oxs1 oxs2 =>
         match oxs1, oxs2 with
         | Some xs1, Some xs2 => Some (Sv.inter xs1 xs2)
         | _ , _ => None
         end) r1.(region_vars) r2.(region_vars) |}.
  
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

Definition mk_ofs aa ws e1 ofs := 
  let sz := mk_scale aa ws in
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
  | None => ok tt
  | Some _ => cerror "not a reg variable"
  end.

Inductive vptr_kind := 
  | VKglob of Z * wsize
  | VKptr  of ptr_kind.

Definition var_kind := option vptr_kind.

Definition with_var xi x := 
  {| v_var := x; v_info := xi.(v_info) |}.

Definition mk_addr_ptr x aa ws (pk:ptr_kind) (e1:pexpr) := 
  match pk with
  | Pstack z _ => ok (with_var x pmap.(vrsp), mk_ofs aa ws e1 z)
  | Pregptr p  => ok (with_var x p,    mk_ofs aa ws e1 0)
  | Pstkptr z  => cerror "stack pointer in expression" 
  end.

Definition mk_addr x aa ws (pk:vptr_kind) (e1:pexpr) := 
  match pk with
  | VKglob z => ok (with_var x pmap.(vrip), mk_ofs aa ws e1 z.1)
  | VKptr pk => mk_addr_ptr x aa ws pk e1
  end.
 
Definition get_var_kind x :=
  let xv := x.(gv) in
  if is_glob x then
    Let z := get_global xv in
    ok (Some (VKglob z))
  else 
    ok (omap VKptr (get_local xv)).

Definition check_vpk_word rmap x vpk ws :=
  Let mp := 
    match vpk with
    | VKglob z => ok (mp_glob pmap.(vrip) z)
    | VKptr pk => check_valid rmap x 
    end in
  check_align mp ws.

Fixpoint alloc_e (e:pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e
  | Pvar   x =>
    let xv := x.(gv) in
    Let vk := get_var_kind x in
    match vk with
    | None => ok e
    | Some vpk => 
      if is_word_type (vtype xv) is Some ws then
        Let _ := check_vpk_word rmap xv vpk ws in
        Let pofs := mk_addr xv AAdirect ws vpk (Pconst 0) in
        ok (Pload ws pofs.1 pofs.2)
      else cerror "not a word variable in expression, please report"
    end

  | Pget aa ws x e1 =>
    let xv := x.(gv) in
    Let e1 := alloc_e e1 in
    Let _ := 
      (* This is not necessary for the proof, it is here just to ensure that 
         the compilation will not fail later *)
      if is_glob x then
        if is_const e1 is Some _ then ok tt
        else cerror "not constant global array index: use pointer"
      else ok tt in
    Let vk := get_var_kind x in
    match vk with
    | None => ok (Pget aa ws x e1)
    | Some vpk => 
      Let _ := check_vpk_word rmap xv vpk ws in
      Let pofs := mk_addr xv aa ws vpk e1 in
      ok (Pload ws pofs.1 pofs.2)
    end             
  | Psub aa ws len x e1 =>
    cerror "Psub"

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

Definition mp_pk pk := 
  match pk with
  | Pstack ofs align => ok (mp_stack pmap.(vrsp) ofs align)
  | _                => cerror "not a pointer to array: please report"
  end.

Definition alloc_lval (rmap: regions) (r:lval) ty := 
  match r with
  | Lnone _ _ => ok (rmap, r)

  | Lvar x =>
    match get_local x with 
    | None => Let _ := check_diff x in ok (rmap, r)
    | Some pk => 
      if is_word_type (vtype x) is Some ws then 
        if ty == sword ws then 
          Let pofs := mk_addr_ptr x AAdirect ws pk (Pconst 0) in
          Let mp   := mp_pk pk in
          let r := Lmem ws pofs.1 pofs.2 in
          Let rmap := Region.set_word rmap x ws mp in
          ok (rmap, r)
        else cerror "invalid type for assignment"
      else cerror "not a word variable in assignment"
    end

  | Laset aa ws x e1 =>
    Let e1 := alloc_e rmap e1 in
    match get_local x with
    | None => Let _ := check_diff x in ok (rmap, Laset aa ws x e1)
    | Some pk => 
      Let mp := check_valid rmap x in
      Let pofs := mk_addr_ptr x aa ws pk e1 in
      let r := Lmem ws pofs.1 pofs.2 in
      Let rmap := Region.set_word rmap x ws mp in
      ok (rmap, r)
    end   
  | Lasub aa ws len x e1 =>
    cerror "Lasub"
  | Lmem ws x e1 =>
    Let _ := check_var x in
    Let e1 := alloc_e rmap e1 in
    ok (rmap, Lmem ws x e1)
  end.

Definition get_Pvar e := 
  match e with
  | Pvar x => ok x 
  | _      => cerror "variable excepted" 
  end.

Definition get_Lvar lv := 
  match lv with
  | Lvar x => ok x
  | _      => cerror "variable excepted"
  end.

Definition nop := Copn [::] AT_none Onop [::]. 

Definition lea_ptr x y ptr ofs := 
  Copn [::x] AT_none (Ox86 (LEA Uptr)) 
       [:: add (Pvar (mk_lvar (with_var y ptr))) (cast_const ofs)].

Definition mov_ptr x y :=
  Copn [:: x] AT_none (Ox86 (MOV Uptr)) [::y].

Definition move_pk pk dx vy := 
  match pk with
  | Pstack ofs _  => lea_ptr dx vy pmap.(vrsp) ofs
  | Pregptr p     => mov_ptr dx (Pvar (mk_lvar (with_var vy p)))
  | Pstkptr z     => mov_ptr dx (Pload Uptr (with_var vy pmap.(vrsp)) (cast_const z))
  end.

Definition get_addr is_spilling rmap x dx y := 
  let vy := y.(gv) in 
  Let ir := 
    if is_glob y then 
      Let ofsa := get_global vy in
      let mpy := (mp_glob pmap.(vrip) ofsa) in
      let ir := 
        if is_spilling then
          match Mvar.get rmap.(var_region) x with
          | None => lea_ptr dx vy pmap.(vrip) ofsa.1
          | Some mpx => if (mpx == mpy) then nop else lea_ptr dx vy pmap.(vrip) ofsa.1 
          end 
        else lea_ptr dx vy pmap.(vrip) ofsa.1 in
      ok (mpy, ir)
    else
      match get_local vy with
      | None => cerror "register array remain" 
      | Some pk => 
        Let mpy := Region.check_valid rmap vy in   
        let ir := 
          if is_spilling then 
            match Mvar.get rmap.(var_region) x with
            | None => move_pk pk dx vy
            | Some mpx => if mpx == mpy then nop else move_pk pk dx vy
            end
          else move_pk pk dx vy
        in
        ok (mpy, ir)
      end in
  let rmap := Region.set rmap x ir.1 in
  ok (rmap, ir.2).

(* Precondition is_sarr ty *)
Definition alloc_array_move rmap r e :=
  Let x := get_Lvar r in
  Let y := get_Pvar e in
  let xk := get_local (v_var x) in
  match xk with
  | None => cerror "register array remains" 
  | Some pk1 =>
    match pk1 with
    | Pstack z1 ws =>
      Let _  := assert (is_lvar y)
                 (Cerr_stk_alloc "invalid move: global to stack") in 
      Let mp := Region.check_valid rmap y.(gv) in
      Let _  := assert (mem_pos_same mp (mp_stack pmap.(vrsp) z1 ws))
                 (Cerr_stk_alloc "invalid move: check alias") in  
      let rmap := Region.set rmap x mp in
      ok (rmap, nop)
    | Pregptr p =>
      get_addr false rmap x (Lvar (with_var x p)) y
    | Pstkptr z =>
      get_addr true rmap x (Lmem Uptr (with_var x pmap.(vrsp)) (cast_ptr z)) y
    end
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

Record stk_alloc_oracle_t :=
  { sao_align : wsize 
  ; sao_size: Z
  ; sao_params : seq (option param_info)  (* Allocation of pointer params *)
  ; sao_return : seq (option nat)         (* Where to find the param input region *)
  ; sao_alloc: seq (var * ptr_kind)       (* Allocation of local variables without params *)
  ; sao_to_save: seq var (* TODO: allocate them in the stack rather than push/pop *)
  ; sao_rsp: saved_stack
  ; sao_return_address: return_address_location
  }.

Section PROG.

Context (local_alloc: funname -> stk_alloc_oracle_t).

Definition alloc_call_arg rmap (sao_param: option param_info) (e:pexpr) := 
  Let x := get_Pvar e in
  Let _ := assert (~~is_glob x) 
                  (Cerr_stk_alloc "global variable in argument of a call") in
  let xv := gv x in
  match sao_param, get_local xv with
  | None, None =>  
    ok (None, Pvar x)
  | None, Some _ => cerror "argument not a reg" 
  | Some pi, Some (Pregptr p) => 
    Let mp := Region.check_valid rmap xv in
    Let _  := if pi.(pp_writable) then writable mp else ok tt in
    Let _  := check_align mp pi.(pp_align) in
    ok (Some (pi.(pp_writable),mp), Pvar (mk_lvar (with_var xv p)))
  | Some _, _ => cerror "the argument should be a reg ptr" 
  end.

Fixpoint check_all_disj (notwritables writables:seq mem_pos) (mps:seq (option (bool * mem_pos) * pexpr)) := 
  match mps with
  | [::] => true
  | (None, _) :: mps => check_all_disj notwritables writables mps
  | (Some (writable, mp), _) :: mps => 
    if mp \in writables then false
    else
      if writable then 
        if (mp \in notwritables) then false
        else check_all_disj notwritables (mp::writables) mps
      else   check_all_disj (mp::notwritables) writables mps
  end.

Definition alloc_call_args rmap (sao_params: seq (option param_info)) (es:seq pexpr) := 
  Let es  := mapM2 (Cerr_stk_alloc "bad params info:please report") (alloc_call_arg rmap) sao_params es in
  Let _ := assert (check_all_disj [::] [::] es) 
           (Cerr_stk_alloc "some writable reg ptr are not disjoints") in
  ok es.

Definition check_lval_reg_call (r:lval) := 
  match r with
  | Lnone _ _ => ok tt
  | Lvar x =>
    match get_local x with 
    | None   => Let _ := check_diff x in ok tt
    | Some _ => cerror "call result should be stored in reg"
    end
  | Laset aa ws x e1 => cerror "array assignement in lval of a call"
  | Lasub aa ws len x e1 => cerror "sub array assignement in lval of a call"
  | Lmem ws x e1     => cerror "call result should be stored in reg"
  end.

Definition check_is_Lvar r (x:var) :=
  match r with
  | Lvar x' => x == x' 
  | _       => false 
  end.

Definition get_regptr (x:var_i) := 
  match get_local x with
  | Some (Pregptr p) => ok (with_var x p)
  | _ => cerror "variable should be a reg ptr" 
  end.

Definition alloc_lval_call (mps:seq (option (bool * mem_pos) * pexpr)) rmap (r: lval) (i:option nat) :=
  match i with
  | None => 
    Let _ := check_lval_reg_call r in
    ok (rmap, r)
  | Some i => 
    match nth (None, Pconst 0) mps i with
    | (Some (_,mp), _) =>
      Let x := get_Lvar r in
      Let p := get_regptr x in
      let rmap := Region.rset_word rmap (v_var x) mp in
      ok (rmap, Lvar p)
    | (None, _) => cerror "alloc_r_call : please report"
    end
  end.

Definition remove_writable_arg rmap (mpe: option (bool * mem_pos) * pexpr) := 
  match mpe.1 with
  | Some(writable, mp) => if writable then Region.remove rmap mp else rmap
  | _                  => rmap
  end.

Definition alloc_call_res rmap mps ret_pos rs := 
  (* remove form rmap all arguments that are writable *)  
  let rmap := foldl remove_writable_arg rmap mps in 
  fmapM2 bad_lval_number (alloc_lval_call mps) rmap rs ret_pos.

Definition alloc_call rmap ini rs fn es := 
  let sao := local_alloc fn in
  Let es  := alloc_call_args rmap sao.(sao_params) es in
  Let rs  := alloc_call_res  rmap es sao.(sao_return) rs in
  let es  := map snd es in
  ok (rs.1, Ccall ini rs.2 fn es).

Fixpoint alloc_i (rmap:regions) (i: instr) : result instr_error (regions * instr) :=
  let (ii, ir) := i in
  Let ir :=
    match ir with
    | Cassgn r t ty e => 
      if is_sarr ty then add_iinfo ii (alloc_array_move rmap r e) 
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
      let check_c rmap := 
        Let c1 := fmapM alloc_i rmap c1 in
        let rmap1 := c1.1 in
        Let e := add_iinfo ii (alloc_e rmap1 e) in
        Let c2 := fmapM alloc_i rmap1 c2 in
        ok ((rmap1, c2.1), (e, (c1.2, c2.2))) in
      Let r := loop2 ii check_c Loop.nb rmap in
      ok (r.1, Cwhile a r.2.2.1 r.2.1 r.2.2.2)

    | Ccall ini rs fn es =>
      add_iinfo ii (alloc_call rmap ini rs fn es) 

    | Cfor _ _ _  => cierror ii (Cerr_stk_alloc "don't deal with for loop")
    end in
  ok (ir.1, MkI ii ir.2).

End PROG.

Definition size_of (t:stype) :=
  match t with
  | sword sz => wsize_size sz
  | sarr n   => Zpos n
  | sbool | sint => 0%Z
  end.

Definition init_local_map vrip vrsp fn
    (ws_align: wsize) (sz:Z) (l:list (var * ptr_kind)) : cfexec (Mvar.t ptr_kind * regions * Sv.t) :=
  let check_diff x := 
    if (x == vrip) || (x == vrsp) then
      cferror fn "invalid reg pointer, please report"
    else ok tt in

  let add_ty x pk ty ws p (mp : Mvar.t ptr_kind * Z * regions * Sv.t) := 
    let '(lmap, ofs, rmap, sv) := mp in
    if (ws <= ws_align)%CMP then
      if (ofs <=? p)%Z then
        if is_align (wrepr _ p) ws then 
          let s := size_of ty in
          ok (Mvar.set lmap x pk, p + s, Region.set_init vrsp rmap x pk, sv)%Z
        else cferror fn "not aligned"
      else cferror fn "overlap"
    else cferror fn "bad stack alignment" in

  let add (vp:var*ptr_kind) (mp:Mvar.t ptr_kind * Z * regions * Sv.t) :=
    let '(v, pk) := vp in
    Let _ := check_diff v in
    match pk with
    | Pstack p ws => add_ty v pk (vtype v)    ws   p mp 
    | Pstkptr p   => add_ty v pk (sword Uptr) Uptr p mp
    | Pregptr x   => 
      let '(lmap, ofs, rmap, sv) := mp in
      Let _ := check_diff x in
      if vtype x == sword Uptr then 
        ok (Mvar.set lmap v pk, ofs, Region.set_init vrsp rmap x pk, Sv.add x sv)%Z    
      else cferror fn "invalid pointer type, please report"
    end in

  let sv := Sv.add vrip (Sv.add vrsp Sv.empty) in
  Let mp := foldM add (Mvar.empty ptr_kind, 0%Z, Region.empty, sv) l in
  let '(lmap, ofs, rmap, sv) := mp in
  if (ofs <=? sz)%Z then ok (lmap, rmap, sv)
  else cferror fn "stack size, please report".

End Section.

(* TODO : move *)
Definition add_err_fun (A : Type) (f : funname) (r : cexec A) :=
  match r with
  | ok _ a => ok a
  | Error e => Error (Ferr_fun f e)
  end.

(** For each function, the oracle returns:
  - the size of the stack block;
  - an allocation for local variables;
  - an allocation for the variables to save;
  - where to save the stack pointer (of the caller); (* TODO: merge with above? *)
  - how to pass the return address (non-export functions only)

  It can call back the partial stack-alloc transformation that given an oracle (size of the stack block and allocation of stack variables)
  will transform the body of the current function.

  The oracle is implemented as follows:
   1/ stack allocation
   2/ Reg allocation
   3/ if we have remaining register to save the stack pointer we use on those register
      else
        4/ we restart stack allocation and we keep one position in the stack to save the stack pointer
        5/ Reg allocation
*)

Definition check_result pmap rmap params oi (x:var_i) := 
  match oi with
  | Some i =>
    match nth None params i with
    | Some mp => 
      Let mp' := check_valid rmap x in
      Let _   := assert (mp == mp') (Cerr_stk_alloc "invalid reg ptr in result") in
      Let p   := get_regptr pmap x in
      ok p
    | None => cerror "invalid function info:please report"
    end
  | None => 
    Let _ := check_var pmap x in
    ok x
  end.

Definition check_results pmap rmap params oi res := 
  mapM2 (Cerr_stk_alloc "invalid function info:please report")
        (check_result pmap rmap params) oi res.

Definition init_param accu pi (x:var_i) := 
  let: (disj, lmap, rmap) := accu in
  match pi with
  | None => ok (accu, (None, x))
  | Some pi => 
    Let _ := assert (vtype pi.(pp_ptr) == sword Uptr) (Cerr_stk_alloc "bad ptr type: please report") in
    Let _ := assert (~~Sv.mem pi.(pp_ptr) disj) (Cerr_stk_alloc "duplicate region: please report") in
    let mp := 
      {| mp_s := pi.(pp_ptr); mp_ofs := 0; mp_align := pi.(pp_align); mp_writable := pi.(pp_writable) |} in
    ok (Sv.add pi.(pp_ptr) disj, 
        Mvar.set lmap x (Pregptr pi.(pp_ptr)),
        rset_word rmap x mp, 
        (Some mp, with_var x pi.(pp_ptr)))
  end. 

Definition init_params vrip vrsp lmap rmap sao_params params :=
  fmapM2 (Cerr_stk_alloc "invalid function info:please report")
    init_param (Sv.add vrip (Sv.singleton vrsp), lmap, rmap) sao_params params.
   
Definition alloc_fd_aux p_extra mglob (local_alloc: funname -> stk_alloc_oracle_t) sao (f: _ufun_decl) : cfexec _ufundef :=
  let: (fn, fd) := f in
  let vrip := {| vtype := sword Uptr; vname := p_extra.(sp_rip) |} in
  let vrsp := {| vtype := sword Uptr; vname := p_extra.(sp_stk_id) |} in
  Let mstk := init_local_map vrip vrsp fn sao.(sao_align) sao.(sao_size) sao.(sao_alloc) in
  let: (lmap, rmap, sv) := mstk in
  (* adding params to the map *)
  Let rparams := 
    add_err_fun fn (init_params vrip vrsp lmap rmap sao.(sao_params) fd.(f_params)) in
  let: (_, lmap, rmap, alloc_params) := rparams in
  let paramsi := map fst alloc_params in
  let params : seq var_i := map snd alloc_params in
  let pmap := {|
        vrip    := vrip;
        vrsp    := vrsp;
        globals := mglob;
        locals  := lmap;
        vnew    := sv;
      |} in
  Let rbody := add_finfo fn fn (fmapM (alloc_i pmap local_alloc) rmap fd.(f_body)) in
  let: (rmap, body) := rbody in
  Let res := 
      add_err_fun fn (check_results pmap rmap paramsi sao.(sao_return) fd.(f_res)) in
  ok {|
    f_iinfo := f_iinfo fd;
    f_tyin := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_params) fd.(f_tyin); 
    f_params := params;
    f_body := body;
    f_tyout := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_return) fd.(f_tyout);
    f_res := res;
    f_extra := f_extra fd |}.

Definition alloc_fd p_extra mglob (local_alloc: funname -> stk_alloc_oracle_t) (f: ufun_decl) :=
  let: sao := local_alloc f.1 in
  Let fd := alloc_fd_aux p_extra mglob local_alloc sao f in
  let f_extra := {|
        sf_align  := sao.(sao_align);
        sf_stk_sz := sao.(sao_size);
        sf_to_save := sao.(sao_to_save);
        sf_save_stack := sao.(sao_rsp);
        sf_return_address := sao.(sao_return_address);
      |} in
  ok (f.1, swith_extra fd f_extra). 

Definition check_glob (m: Mvar.t (Z*wsize)) (data:seq u8) (gd:glob_decl) := 
  let x := gd.1 in
  match Mvar.get m x with
  | None => false 
  | Some (z, _) =>
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
             match WArray.get AAdirect U8 t (Z.of_nat i) with
             | Ok w => nth 0%R data i == w
             | _    => false
             end) (iota 0 s)
    end
  end.

Definition check_globs (gd:glob_decls) (m:Mvar.t (Z*wsize)) (data:seq u8) := 
  all (check_glob m data) gd.

Definition init_map (sz:Z) (l:list (var * (Z * wsize) )) : cexec (Mvar.t (Z*wsize)) :=
  let add (vp:var*(Z*wsize)) (mp:Mvar.t (Z*wsize) * Z) :=
    let: (v, (p, ws)) := vp in
    if (mp.2 <=? p)%Z then
      let ty := vtype v in
      if is_align (wrepr _ p) ws then
        let s := size_of ty in
        cok (Mvar.set mp.1 v (p,ws), p + s)%Z
      else cerror "bad global alignment: please report"
    else cerror "global overlap: please report" in
  Let mp := foldM add (Mvar.empty (Z*wsize), 0%Z) l in
  if (mp.2 <=? sz)%Z then cok mp.1
  else cerror "global size:please report".

Definition alloc_prog nrsp rip global_data global_alloc local_alloc (P:uprog) :=
  Let mglob := add_err_msg (init_map (Z.of_nat (size global_data)) global_alloc) in
  let p_extra :=  {|
    sp_rip   := rip;
    sp_globs := global_data;
    sp_stk_id := nrsp;
  |} in
  if rip == nrsp then Error (Ferr_msg (Cerr_stk_alloc "rip and rsp clash, please report"))
  else if check_globs P.(p_globs) mglob global_data then
    Let p_funs := mapM (alloc_fd p_extra mglob local_alloc) P.(p_funcs) in
    ok  {| p_funcs  := p_funs;
           p_globs := [::];
           p_extra := p_extra;
        |}
  else 
     Error (Ferr_msg (Cerr_stk_alloc "invalid data: please report")).
