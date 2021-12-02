From mathcomp Require Import all_ssreflect all_algebra.
Require Import low_memory expr x86_sem compiler_util lowering x86_variables.
Import Utf8.
Import oseq.
Import GRing.
Require Import ssrring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pexpr_of_lval ii (lv:lval) : cexec pexpr :=
  match lv with
  | Lvar x          => ok (Plvar x)
  | Lmem s x e      => ok (Pload s x e)
  | Lnone _ _       => Error (E.internal_error ii "_ lval remains")
  | Laset _ _ _ _   => Error (E.internal_error ii "Laset lval remains")
  | Lasub _ _ _ _ _ => Error (E.internal_error ii "Lasub lval remains")
  end.

Definition nmap (T:Type) := nat -> option T.
Definition nget (T:Type) (m:nmap T) (n:nat) := m n.
Definition nset (T:Type) (m:nmap T) (n:nat) (t:T) :=
  fun x => if x == n then Some t else nget m x.
Definition nempty (T:Type) := fun n:nat => @None T.

Definition var_of_implicit (i:implicit_arg) :=
  match i with
  | IArflag f => var_of_flag f
  | IAreg r   => var_of_register r
  end.

Definition assemble_lea ii lea :=
  Let base := reg_of_ovar ii lea.(lea_base) in
  Let offset := reg_of_ovar ii lea.(lea_offset) in
  Let scale := scale_of_z' ii lea.(lea_scale) in
  ok (Areg {|
      ad_disp := lea.(lea_disp);
      ad_base := base;
      ad_scale := scale;
      ad_offset := offset
    |}).

Definition addr_of_pexpr (rip:var) ii sz (e: pexpr) :=
  Let _ := assert (sz <= Uptr)%CMP
                  (E.error ii (pp_s "Bad type for address")) in
  match lowering.mk_lea sz e with
  | Some lea =>
     match lea.(lea_base) with
     | Some r =>
        if r.(v_var) == rip then
          Let _ := assert (lea.(lea_offset) == None)
                          (E.error ii (pp_box [::pp_s "Invalid global address :"; pp_e e])) in
           ok (Arip lea.(lea_disp))
        else assemble_lea ii lea
      | None =>
        assemble_lea ii lea
      end
  | None => Error (E.error ii (pp_box [::pp_s "not able to assemble address :"; pp_e e]))
  end.

Definition addr_of_xpexpr rip ii sz v e :=
  addr_of_pexpr rip ii sz (Papp2 (Oadd (Op_w sz)) (Plvar v) e).

Definition assemble_word_mem rip ii (sz:wsize) (e:pexpr) :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) =>
    let w := wrepr sz' z in
    let w1 := sign_extend sz w in
    let w2 := wrepr sz z in
    (* this check is not used (yet?) in the correctness proof *)
    Let _ := assert (w1 == w2)
                    (E.werror ii e "out of bound constant") in
    ok (Imm w)
  | Pvar x =>
    Let _ := assert (is_lvar x)
                    (E.internal_error ii "Global variables remain") in
    let x := x.(gv) in
    xreg_of_var ii x
  | Pload sz' v e' =>
    Let _ := assert (sz == sz')
                    (E.werror ii e "invalid Load size") in
    Let w := addr_of_xpexpr rip ii Uptr v e' in
    ok (Addr w)
  | _ => Error (E.werror ii e "invalid pexpr for word")
  end.

Definition assemble_word (k:addr_kind) rip ii (sz:wsize) (e:pexpr) :=
  match k with
  | AK_mem => assemble_word_mem rip ii (sz:wsize) (e:pexpr)
  | AK_compute =>
    Let w := addr_of_pexpr rip ii sz e in
    ok (Addr w)
  end.

Definition arg_of_pexpr k rip ii (ty:stype) (e:pexpr) :=
  match ty with
  | sbool => Let c := assemble_cond ii e in ok (Condt c)
  | sword sz => assemble_word k rip ii sz e
  | sint  => Error (E.werror ii e "not able to assemble an expression of type int")
  | sarr _ => Error (E.werror ii e "not able to assemble an expression of type array _")
  end.

Definition compile_arg rip ii (ade: (arg_desc * stype) * pexpr) (m: nmap asm_arg) : cexec (nmap asm_arg) :=
  let ad := ade.1 in
  let e := ade.2 in
  match ad.1 with
  | ADImplicit i =>
    Let _ :=
      assert (eq_expr (Plvar (VarI (var_of_implicit i) xH)) e)
             (E.internal_error ii "(compile_arg) bad implicit register") in
    ok m
  | ADExplicit k n o =>
    Let a := arg_of_pexpr k rip ii ad.2 e in
    Let _ :=
      assert (check_oreg o a)
             (E.internal_error ii "(compile_arg) bad forced register") in
    match nget m n with
    | None => ok (nset m n a)
    | Some a' =>
      if a == a' then ok m
      else Error (E.internal_error ii "(compile_arg) not compatible asm_arg")
    end
  end.

Definition compile_args rip ii adts (es:pexprs) (m: nmap asm_arg) :=
  foldM (compile_arg rip ii) m (zip adts es).

Definition compat_imm ty a' a := 
  (a == a') || match ty, a, a' with
             | sword sz, Imm sz1 w1, Imm sz2 w2 => sign_extend sz w1 == sign_extend sz w2
             | _, _, _ => false
             end.

Definition check_sopn_arg rip ii (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) xH))
  | ADExplicit k n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr k rip ii adt.2 x is Ok a' then compat_imm adt.2 a a' && check_oreg o a
      else false
    | None => false
    end
  end.

Definition check_sopn_dest rip ii (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) xH))
  | ADExplicit _ n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr AK_mem rip ii adt.2 x is Ok a' then (a == a') && check_oreg o a
      else false
    | None => false
    end
  end.

Definition error_imm ii :=
 E.error ii (pp_s "Invalid asm: cannot truncate the immediate to a 32 bits immediate, move it to a register first").

Definition assemble_x86_opn_aux rip ii op (outx : lvals) (inx : pexprs) :=
  let id := instr_desc op in
  Let m := compile_args rip ii (zip id.(id_in) id.(id_tin)) inx (nempty _) in
  Let eoutx := mapM (pexpr_of_lval ii) outx in
  Let m := compile_args rip ii (zip id.(id_out) id.(id_tout)) eoutx m in
  match oseq.omap (nget m) (iota 0 id.(id_nargs)) with
  | None => Error (E.internal_error ii "compile_arg : assert false nget")
  | Some asm_args => ok asm_args
  end.

Definition check_sopn_args rip ii (loargs : seq asm_arg) (xs : seq pexpr) (adt : seq (arg_desc * stype)) :=
  all2 (check_sopn_arg rip ii loargs) xs adt.

Definition check_sopn_dests rip ii (loargs : seq asm_arg) (outx : seq lval) (adt : seq (arg_desc * stype)) :=
  match mapM (pexpr_of_lval ii) outx with
  | Ok eoutx => all2 (check_sopn_dest rip ii loargs) eoutx adt
  | _  => false
  end.

(* [check_arg_kind] but ignore constraints on immediate sizes *)
Definition check_arg_kind_no_imm (a:asm_arg) (cond: arg_kind) :=
  match a, cond with
  | Condt _, CAcond => true
  | Imm _ _, CAimm _ => true
  | Reg _, CAreg => true
  | Addr _, CAmem _ => true
  | XReg _, CAxmm   => true
  | _, _ => false
  end.

(* Keep only the elements of [cond] that are compatible with [a].
   If the resulting list is empty, this means that no element of [cond] is
   compatible, and we return an error. This error is systematically caught by
   [filter_args_kinds_no_imm], thus we don't need a real error message, that's
   why we use [tt] as the error.
*)
Definition filter_arg_kinds_no_imm (a:asm_arg) (cond:arg_kinds) :=
  let cond' : arg_kinds := filter (check_arg_kind_no_imm a) cond in
  if cond' is [::] then Error tt else ok cond'.

(* We use [mapM2] so that we check that the two lists have equal lengths.
   But we don't need a real error message, thus we use [tt] as the error. *)
Definition filter_args_kinds_no_imm (args:asm_args) (cond:args_kinds) : option args_kinds :=
  match mapM2 tt (fun a c => filter_arg_kinds_no_imm a c) args cond with
  | Ok cond => Some cond
  | _ => None
  end.

Definition filter_i_args_kinds_no_imm (cond:i_args_kinds) (a:asm_args) : i_args_kinds :=
  pmap (filter_args_kinds_no_imm a) cond.

(* Enforce size constraints on immediates. *)
Definition enforce_imm_arg_kind (a:asm_arg) (cond: arg_kind) : option asm_arg :=
  match a, cond with
  | Condt _, CAcond => Some a
  | Imm sz w, CAimm sz' =>
    let w1 := zero_extend sz' w in
    let w2 := sign_extend sz w1 in
    (* this check is not used (yet?) in the correctness proof *)
    if w == w2 then Some (Imm w1) else None
  | Reg _, CAreg => Some a
  | Addr _, CAmem _ => Some a
  | XReg _, CAxmm   => Some a
  | _, _ => None
  end.

Definition enforce_imm_arg_kinds (a:asm_arg) (cond:arg_kinds) :=
  find_map (enforce_imm_arg_kind a) cond.

(* We use [mapM2] so that we check that the two lists have equal lengths.
   But we don't need a real error message, thus we use [tt] as the error. *)
Definition enforce_imm_args_kinds (args:asm_args) (cond:args_kinds) : option asm_args :=
  match mapM2 tt (fun a c => o2r tt (enforce_imm_arg_kinds a c)) args cond with
  | Ok args => Some args
  | _ => None
  end.

Definition enforce_imm_i_args_kinds (cond:i_args_kinds) (a:asm_args) :=
  find_map (enforce_imm_args_kinds a) cond.

Definition pp_arg_kind c :=
  match c with
  | CAmem b => pp_nobox [:: pp_s "mem (glob "; pp_s (if b then "" else "not ")%string; pp_s "allowed)"]
  | CAimm ws => pp_nobox [:: pp_s "imm "; pp_s (string_of_wsize ws)]
  | CAcond => pp_s "cond"
  | CAreg => pp_s "reg"
  | CAxmm => pp_s "xreg"
  end.

Fixpoint pp_list {A} sep (pp : A -> pp_error) xs : seq pp_error :=
  match xs with
  | [::] => [::]
  | [:: x] => [:: pp x]
  | x :: xs => pp x :: sep :: (pp_list sep pp xs)
  end.

Definition pp_arg_kinds cond :=
  pp_box [:: pp_nobox (pp_s "[" :: pp_list (pp_nobox [:: pp_s ";"; PPEbreak]) pp_arg_kind cond ++ [:: pp_s "]"])].

Definition pp_args_kinds cond :=
  pp_box [:: pp_nobox (pp_s "[" :: pp_list (pp_nobox [:: pp_s ";"; PPEbreak]) pp_arg_kinds cond ++ [:: pp_s "]"])].

Definition pp_i_args_kinds cond :=
  pp_vbox [:: pp_nobox (pp_list PPEbreak pp_args_kinds cond)].

Definition assemble_x86_opn rip ii op (outx : lvals) (inx : pexprs) := 
  let id := instr_desc op in
  Let asm_args := assemble_x86_opn_aux rip ii op outx inx in
  let s := id.(id_str_jas) tt in
  let args_kinds := filter_i_args_kinds_no_imm id.(id_args_kinds) asm_args in
  Let _ := assert (args_kinds != [::])
                  (E.error ii (pp_nobox [::
                    pp_box [:: pp_s "instruction"; pp_s s; pp_s "is given incompatible args."]; PPEbreak;
                    pp_vbox [::
                      pp_s "Allowed args are:";
                      pp_nobox [:: pp_s "  "; pp_i_args_kinds id.(id_args_kinds)]]])) in
  Let asm_args :=
    if enforce_imm_i_args_kinds args_kinds asm_args is Some asm_args then
      ok asm_args
    else
      Error (E.error ii (pp_nobox [::
        pp_box [:: pp_s "instruction"; pp_s s; pp_s "is given at least one too large immediate as an argument."]; PPEbreak;
        pp_vbox [::
        pp_s "Allowed args compatible with the input (except on immediate sizes) are:";
        pp_nobox [::pp_s "  "; pp_vbox [::
        pp_i_args_kinds args_kinds]];
        pp_s "All allowed args (regardless of the input) are:";
        pp_nobox [:: pp_s "  "; pp_vbox [::
        pp_i_args_kinds id.(id_args_kinds)]]]]))
  in
  Let _ := assert (check_sopn_args rip ii asm_args inx (zip id.(id_in) id.(id_tin)) &&
                     check_sopn_dests rip ii asm_args outx (zip id.(id_out) id.(id_tout)))
                  (E.internal_error ii "assemble_x86_opn: cannot check") in
  ok (op.2, asm_args).

Definition assemble_sopn rip ii op (outx : lvals) (inx : pexprs) :=
  match op with
  | Ocopy _ _ 
  | Onop
  | Omulu     _ 
  | Oaddcarry _ 
  | Osubcarry _ =>
    Error (E.internal_error ii "assemble_sopn : invalid op")
  (* Low level x86 operations *)
  | Oset0 sz => 
    let op := if (sz <= U64)%CMP then (XOR sz) else (VPXOR sz) in
    Let x := 
      match rev outx with 
      | Lvar x :: _ =>  ok x
      | _ => Error (E.internal_error ii "set0 : destination is not a register")
      end in
    assemble_x86_opn rip ii (None, op) outx [::Plvar x; Plvar x]
  | Ox86MOVZX32 =>
    Let x := 
      match outx with 
      | [::Lvar x] =>  ok x
      | _ => Error (E.internal_error ii "Ox86MOVZX32: destination is not a register")
      end in
    assemble_x86_opn rip ii (None, MOV U32) outx inx

  | Oconcat128 =>
    Let inx := 
        match inx with
        | [:: h; Pvar _ as l] => ok [:: l; h; @wconst U8 1%R]
        |  _ => Error (E.internal_error ii "Oconcat: assert false")
        end in
    assemble_x86_opn rip ii (None, VINSERTI128) outx inx
    
  | Ox86' op =>
    assemble_x86_opn rip ii op outx inx 
  end.

Lemma id_semi_sopn_sem op :
  let id := instr_desc op in
  id_semi id = sopn_sem (Ox86' op).
Proof. by []. Qed.
