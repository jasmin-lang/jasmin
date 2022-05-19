From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require oseq.
Require Import ZArith
utils
strings wsize
memory_model
gen_map
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type
syscall
arch_decl
label
values.

(* FIXME remove this: it is needed due to find_label. so move find label *)
Require Import arch_sem_no_spec.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Variant sec_ty := 
  | Public
(*  | Transient  *)
  | Secret.

Scheme Equality for sec_ty.

Lemma sec_ty_eq_axiom : Equality.axiom sec_ty_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_sec_ty_dec_bl.
  by apply: internal_sec_ty_dec_lb.
Qed.

Definition sec_ty_eqMixin     := Equality.Mixin sec_ty_eq_axiom.
Canonical  sec_ty_eqType      := Eval hnf in EqType sec_ty sec_ty_eqMixin.

Module CmpSecTy.

  Definition t : eqType := [eqType of sec_ty].

  Definition cmp (x y: t) : comparison := 
    match x, y with 
    | Public, Public => Eq 
    | Public, _      => Lt
 (*   | Transient, Public => Gt
    | Transient, Transient => Eq 
    | Transient, Secret => Lt *)
    | Secret, Secret => Eq 
    | Secret, _ => Gt
    end.

  Instance cmpO : Cmp cmp.
  Proof.
    constructor.
    + by move=> [] [].
    + by move=> [] [] [] c //= [].
    by move=> [] [].
  Qed.

End CmpSecTy.

(* ----------------------------------------------------------------- *)

Definition lvl := positive.

Definition public : lvl := 1%positive.
(* Definition transient : lvl := 2%positive. *)
Definition secret : lvl := 3%positive.

Module Ml := Mmake CmpPos.

Module Sl := Smake CmpPos.

Definition spublic := Sl.singleton public.

Definition pointsto := positive.

(* Set of constraints *)
Definition constraints := Ml.t Sl.t.

Definition successors (c:constraints) (l:lvl) := 
  odflt Sl.empty (Ml.get c l).

Definition is_le (c:constraints) (l1 l2:lvl) : bool := 
  Sl.mem l2 (successors c l1).
  (* || l1 == public || l2 == secret *)

Definition le_all (c:constraints) (l:lvl) (S:Sl.t) :=
  (* Sl.for_all (fun l' => is_le c l l') S. *)
  Sl.subset S (successors c l).

Definition is_clos_trans (c:constraints) := 
  forall x y z, 
    is_le c x y -> 
    is_le c y z -> 
    is_le c x z.

Definition check_clos_trans (c:constraints) := 
  Ml.all (fun l1 s => 
               Sl.for_all (fun l2 => Sl.subset (successors c l2) s) s) c.

(* TODO : forall c, check_clos_trans c -> is_clos_trans c *)

Record valid_c (c: constraints) := {
  vc_ct : is_clos_trans c;
  vc_bla (* FIXME *) : ~(is_le c secret public)
    (* ~(is_le c transient public) /\ ~(is_le c secret transient) *)
}.

Section TY_SYS.

Context {reg regx xreg rflag cond asm_op} {asm_d : asm reg regx xreg rflag cond asm_op}. 

Record env_t := 
  { e_reg  : FinMap.map (T:= reg_t)  (lvl * wsize);
    e_regx : FinMap.map (T:= regx_t) (lvl * wsize);
    e_xreg : FinMap.map (T:= xreg_t) (lvl * wsize);
    e_flag : FinMap.map (T:= rflag_t) lvl;
    e_pt   : Mp.t lvl;
 }.

Definition get_pt env pt := odflt secret (Mp.get env.(e_pt) pt).

Definition set_reg env r lw := 
  {| e_reg  := FinMap.set env.(e_reg) r lw;
     e_regx := env.(e_regx);
     e_xreg := env.(e_xreg);
     e_flag := env.(e_flag);
     e_pt   := env.(e_pt);
  |}. 

Definition set_regx env r lw := 
  {| e_reg  := env.(e_reg);
     e_regx := FinMap.set env.(e_regx) r lw;
     e_xreg := env.(e_xreg);
     e_flag := env.(e_flag);
     e_pt   := env.(e_pt);
  |}.

Definition set_xreg env r lw := 
  {| e_reg  := env.(e_reg);
     e_regx := env.(e_regx);
     e_xreg := FinMap.set env.(e_xreg) r lw;
     e_flag := env.(e_flag);
     e_pt   := env.(e_pt);
  |}.

Definition set_flag env r l := 
  {| e_reg  := env.(e_reg); 
     e_regx := env.(e_regx);
     e_xreg := env.(e_xreg);
     e_flag := FinMap.set env.(e_flag) r l;
     e_pt   := env.(e_pt);
  |}.

Definition set_pt env r l := 
  {| e_reg  := env.(e_reg);
     e_regx := env.(e_regx);
     e_xreg := env.(e_xreg);
     e_flag := env.(e_flag);
     e_pt   := Mp.set env.(e_pt) r l;
  |}.

Definition le_ws c (lw1 lw2 : lvl * wsize) := 
  is_le c lw1.1 lw2.1 && (lw2.2 <= lw1.2)%CMP.

Definition le_env c (env1 env2: env_t) := 
  [/\ forall r, le_ws c (env1.(e_reg) r) (env2.(e_reg) r), 
      forall r, le_ws c (env1.(e_regx) r) (env2.(e_regx) r), 
      forall r, le_ws c (env1.(e_xreg) r) (env2.(e_xreg) r), 
      forall r, is_le c (env1.(e_flag) r) (env2.(e_flag) r) &
      forall r, is_le c (get_pt env1 r) (get_pt env2 r)].

(* pt_size : size in bytes of a points-to *)
Definition pt_size := Mp.t positive.
Definition pt_info := option pointsto.

(* Type system for arguments *)

(* Gamma |- e : ty, lvl <= S *)

Context (wt_cond : constraints -> env_t -> cond_t -> Sl.t -> bool).

Section Expr.

Context (c:constraints) (env:env_t).

Definition wt_oreg (ws:wsize) (o:option reg_t) (S:Sl.t) := 
  match o with 
  | Some r => 
      let (lr, ws') := env.(e_reg) r in
      le_all c lr S && (ws <= ws')%CMP
  | None => true
  end.
  
Definition wt_addr (ws:wsize) (a:address) (S:Sl.t) := 
  match a with
  | Areg ra => wt_oreg ws ra.(ad_base) S && wt_oreg ws ra.(ad_offset) S
  | Arip _ => le_all c public S
  end.

Definition wt_asm_arg (k:addr_kind) (a:asm_arg) (ty:stype) (pti:pt_info) (S:Sl.t) := 
  match a, ty with
  | Condt cond, sbool => wt_cond c env cond S

  | Imm _ _, sword _ => le_all c public S

  | Reg r, sword ws  => 
    let (lr, ws') := env.(e_reg) r in
    le_all c lr S && (ws <= ws')%CMP

  | Regx r, sword ws  => 
    let (lr, ws') := env.(e_regx) r in
    le_all c lr S && (ws <= ws')%CMP

  | XReg r, sword ws  => 
    let (lr, ws') := env.(e_xreg) r in
    le_all c lr S && (ws <= ws')%CMP

  | Addr a, sword ws =>
    if k is AK_compute then wt_addr ws a S
    else 
      wt_addr Uptr a spublic &&
      match pti with
      | None => false (* error need a pt_info *)
      | Some pt =>
        let lr := get_pt env pt in 
        le_all c lr S
      end
  | _, _ => false
  end.

Definition wt_implicit_arg (a:implicit_arg) (ty:stype) (S:Sl.t) := 
  match a, ty with 
  | IArflag r, _ => 
    let lr := env.(e_flag) r in
    le_all c lr S 
    (* FIXME share the code with wt_asm_arg *)
  | IAreg r, sword ws =>
    let (lr, ws') := env.(e_reg) r in
    le_all c lr S && (ws <= ws')%CMP
  | _, _ => false
  end.

Definition wt_arg_in (args:asm_args) (S:Sl.t) (a:arg_desc) (pt: pt_info) (ty : stype) := 
  match a with
  | ADImplicit a => wt_implicit_arg a ty S
  | ADExplicit k i _ => 
    match onth args i with
    | None => false
    | Some a => wt_asm_arg k a ty pt S
    end
  end.

(* move this to util *)
Section ALL3.

Context (A B C:Type) (f:A -> B -> C -> bool).

Fixpoint all3 la lb lc := 
  match la, lb, lc with
  | [::], [::], [::] => true
  | a::la, b::lb, c::lc => f a b c && all3 la lb lc
  | _, _, _ => false
  end.

End ALL3.

Definition wt_args_in (args:asm_args) (S:Sl.t) (a:seq arg_desc) (pt: seq pt_info) (ty:seq stype) :=
  all3 (wt_arg_in args S) a pt ty.
  
End Expr.

(* Precomputation of the levels for destination *)

Definition dest_implicit_lvl (env':env_t) (a:implicit_arg) := 
  match a with
  | IArflag r => env'.(e_flag) r 
  | IAreg r => (env'.(e_reg) r).1
  end.

Definition dest_explicite_lvl (env':env_t) (pti : pt_info) (a:asm_arg) := 
  match a with 
  | Condt _ | Imm _ _ => secret (* This is a dummy value, this can not be a destination *)

  | Reg r  => (env'.(e_reg)  r).1
  | Regx r => (env'.(e_regx) r).1
  | XReg r => (env'.(e_xreg) r).1
  | Addr a => 
    match pti with
    | None => secret (* dummy value *)
    | Some pt => get_pt env' pt
    end
  end.

Definition dest_lvl (env': env_t) (args:asm_args) (pti:seq pt_info) (a:arg_desc) := 
  match a with
  | ADImplicit a => dest_implicit_lvl env' a
  | ADExplicit _ i _ => 
    match onth args i with
    | None => secret (* dummy value *)
    | Some a => dest_explicite_lvl env' (nth None pti i) a
    end
  end.

Definition dests_lvl env' args pti (a:seq arg_desc) := 
  map (dest_lvl env' args pti) a.

(* Type checking of destination *)

Definition set_size msb (ws:wsize) (dest_size:wsize) := 
  if msb is MSB_MERGE then min ws dest_size 
  else dest_size.

Definition ty_dest_implicit (msb:msb_flag) (env:env_t) (a:implicit_arg) (l:lvl) (ty:stype) : result unit env_t := 
  match a, ty with
  | IArflag r, sbool => ok (set_flag env r l) 
  | IAreg r, sword ws => ok (set_reg env r (l, set_size msb ws reg_size))
  | _, _ => Error tt
  end.

Definition get_size (pts:pt_size) (pt:pointsto) := 
   match Mp.get pts pt with 
   | None => 0%Z
   | Some p => Zpos p
   end.

Definition ty_dest_explicit (c:constraints) (pts:pt_size) (msb:msb_flag) (env:env_t) (a:asm_arg) (pti:pt_info) (l:lvl) (ty:stype) : result unit env_t:= 
  match a, ty with
  | Reg  r, sword ws => ok (set_reg env r (l, set_size msb ws reg_size))
  | Regx r, sword ws => ok (set_regx env r (l, set_size msb ws regx_size))
  | XReg r, sword ws => ok (set_xreg env r (l, set_size msb ws xreg_size))
  | Addr a, sword ws =>
    match pti with
    | None => Error tt
    | Some pt => 
      let sz := get_size pts pt in 
      let wsz := wsize_size ws in
      if (sz <= wsz)%CMP || is_le c (get_pt env pt) l then ok (set_pt env pt l)
      else Error tt 
    end
  | _, _ => Error tt
  end.

Definition ty_dest (c:constraints) (pts:pt_size) (msb:msb_flag) (args:asm_args) (a:arg_desc) (pti:pt_info) (l:lvl) (ty:stype) (env:env_t) := 
  match a with 
  | ADImplicit a => ty_dest_implicit msb env a l ty 
  | ADExplicit _ i _ => 
    match onth args i with 
    | None => Error tt 
    | Some a => ty_dest_explicit c pts msb env a pti l ty
    end
  end.

Section FoldM4. 

Context (A B C D E R:Type) (f: A -> B -> C -> D -> R -> result E R) (e:E).

Fixpoint foldM4 (la:seq A) (lb: seq B) (lc: seq C) (ld: seq D) r :=
  match la, lb, lc, ld with
  | [::] , [::] , [::] , [::]  => ok r
  | a::la, b::lb, c::lc, d::ld => f a b c d r >>= (foldM4 la lb lc ld)
  | _    , _    , _    , _     => Error e
    end.

End FoldM4.

Definition ty_dests (c:constraints) (pts:pt_size) (msb:msb_flag) (args:asm_args) (a:seq arg_desc) (pti:seq pt_info) (l:seq lvl) (ty:seq stype) (env:env_t) :=
  foldM4 (ty_dest c pts msb args) tt a pti l ty env.

(* FIXME add of_list in Smake *)

Definition of_list (l:seq lvl) := 
  foldl (fun S l => Sl.add l S) Sl.empty l.

(* *************************************** *)

Section Typing.

Context (fn:funname).

Inductive WT_pc (c:constraints) (pts: pt_size) (Env: seq env_t) (Pt_info : seq (seq pt_info * seq pt_info)) (code: asm_code) (pc:nat) : Prop := 
  | WT_AsmOp : forall o args env env' dpt apt env1,
        oseq.onth code pc = Some (AsmOp o args) ->
        oseq.onth Env pc  = Some env -> 
        oseq.onth Env (pc.+1) = Some env' -> 
        nth ([::], [::]) Pt_info pc = (dpt, apt) ->
        let odesc := instr_desc_op o in
        let ls := dests_lvl env' args dpt odesc.(id_out) in
        wt_args_in c env args (of_list ls) odesc.(id_in) apt odesc.(id_tin) -> 
        ty_dests c pts odesc.(id_msb_flag) args odesc.(id_out) dpt ls odesc.(id_tout) env = ok env1 ->
        le_env c env1 env' -> 
        WT_pc c pts Env Pt_info code pc
  | WT_ALIGN : forall env env',
        oseq.onth code pc = Some ALIGN ->
        oseq.onth Env pc  = Some env -> 
        oseq.onth Env (pc.+1) = Some env' -> 
        le_env c env env' ->
        WT_pc c pts Env Pt_info code pc
  | WT_LABEL : forall env env' lbl,
        oseq.onth code pc = Some (LABEL lbl) ->
        oseq.onth Env pc  = Some env -> 
        oseq.onth Env (pc.+1) = Some env' -> 
        le_env c env env' ->
        WT_pc c pts Env Pt_info code pc
  | WT_JMP : forall env env' fn' lbl ip,
        oseq.onth code pc = Some (JMP (fn', lbl)) ->
        oseq.onth Env pc  = Some env -> 
        fn == fn' ->
        find_label lbl code = ok ip -> 
        (*oseq.onth Env ip = Some env' -> *)
        oseq.onth Env ip.+1 = Some env' ->
        le_env c env env' ->
        WT_pc c pts Env Pt_info code pc
  | WT_JCC : forall env envf envt lbl ip ct,
        oseq.onth code pc = Some (Jcc lbl ct) ->
        oseq.onth Env pc  = Some env -> 
        wt_cond c env ct spublic ->
        find_label lbl code = ok ip -> 
        oseq.onth Env (pc.+1) = Some envf -> 
        oseq.onth Env ip = Some envt -> 
        le_env c env envf /\ le_env c env envt ->
        WT_pc c pts Env Pt_info code pc.

(*Definition wt_pc (c:constraints) (pts: pt_size) (Env: seq env_t) (Pt_info : seq (seq pt_info * seq pt_info)) (code: asm_code) (pc:nat) : Prop := 
  if oseq.onth code pc is Some i then 
    if oseq.onth Env pc is Some env then 
       match i with 
       | AsmOp o args => 
           if oseq.onth Env (pc.+1) is Some env' then
             let (dpt, apt) := nth ([::], [::]) Pt_info pc in 
             let odesc := instr_desc_op o in
             let ls := dests_lvl env' args dpt odesc.(id_out) in
             if wt_args_in c env args (of_list ls) odesc.(id_in) apt odesc.(id_tin) then
               match ty_dests c pts odesc.(id_msb_flag) args odesc.(id_out) dpt ls odesc.(id_tout) env with
               | Ok env1 => le_env c env1 env' 
               | _ => false
               end
             else false
           else false

       | ALIGN | LABEL _ => 
         if oseq.onth Env (pc.+1) is Some env' then le_env c env env'
         else false

       | JMP (fn', lbl) => 
         if fn == fn' then 
           match find_label lbl code with 
           | Ok ip => 
             if oseq.onth Env ip is Some env' then le_env c env env'
             else false
           | _ => false
           end
         else false (* FIXME this is a function call *)
              
       | Jcc lbl ct => 
           if wt_cond c env ct spublic then
             match find_label lbl code with
             | Ok ip =>
                 if oseq.onth Env (pc.+1) is Some envf then
                   if oseq.onth Env ip is Some envt then
                     le_env c env envf /\ le_env c env envt 
                   else false
                 else false  
             | _ => false
             end
           else false

       | _ => false
       end
    else false     
  else false.*)

Definition wt_code (c:constraints) (pts: pt_size) (Env: seq env_t) (Pt_info : seq (seq pt_info * seq pt_info)) (code: asm_code) := 
  forall pc,  0 <= pc < size code -> WT_pc c pts Env Pt_info code pc.

(* Proofs *)

Definition valuation := lvl -> sec_ty.

Definition valid_valuation (c:constraints) (rho: valuation) := 
  rho public = Public /\
  rho secret = Secret /\
  forall l s, is_le c l s -> (rho l <= rho s)%CMP.

(* starting address of pointsto *)
Definition vpointsto := pointsto -> option pointer. 

(* two memory areas should be disjoint *) 
Definition wf_vpointsto (vp:vpointsto) :=
forall (pt1:pointsto) (pt2:pointsto) a1 a2 (pts:pt_size),
(pt1 <> pt2)%positive ->
vp pt1 = Some a1 /\ vp pt2 = Some a2 ->
disjoint_zrange a1 (get_size pts pt1) a2 (get_size pts pt2).

(* state equivalence *) 
Inductive state_equiv (rho: valuation) (s1 s2:asm_state) (env: env_t): Prop :=
| asm_st_equiv : 
  s1.(asm_c) = s2.(asm_c) -> 
  s1.(asm_ip) = s2.(asm_ip) -> 
  (forall r l ws, env.(e_reg) r = (l, ws) -> 
   rho l = Public -> 
   zero_extend ws (s1.(asm_m).(asm_reg) r) =
   zero_extend ws (s2.(asm_m).(asm_reg) r)) ->
  (forall r l ws, env.(e_regx) r = (l, ws) -> 
   rho l = Public -> 
   zero_extend ws (s1.(asm_m).(asm_regx) r) =
   zero_extend ws (s2.(asm_m).(asm_regx) r)) ->
  (forall r l ws, env.(e_xreg) r = (l, ws) -> 
   rho l = Public -> 
   zero_extend ws (s1.(asm_m).(asm_xreg) r) =
   zero_extend ws (s2.(asm_m).(asm_xreg) r)) ->
  (forall f l, env.(e_flag) f = l -> 
   rho l = Public -> 
   (s1.(asm_m).(asm_flag) f) = (s2.(asm_m).(asm_flag) f)) ->
  (forall pt l a vp pts, 
   wf_vpointsto vp ->
   vp pt = Some a ->
   get_pt env pt = l -> 
   rho l = Public ->
   (forall i, (0 <= i <= get_size pts pt)%Z -> 
    read (s1.(asm_m).(asm_mem)) (a+word_of_scale (Z.to_nat i))%R = 
    read (s2.(asm_m).(asm_mem)) (a+word_of_scale (Z.to_nat i))%R)) ->
  state_equiv rho s1 s2 env. 

Lemma zero_extend_small_size : forall s sz sz' (w1: word s) (w2: word s),
(sz <= sz')%CMP -> 
zero_extend sz' w1 = zero_extend sz' w2 ->
zero_extend sz  w1 = zero_extend sz  w2.
Proof.
move=> s sz sz' w1 w2 hsz ht.
have hz := zero_extend_idem. move: (hz s sz sz' w1 hsz)=> <-.
move: (hz s sz sz' w2 hsz)=> <-. by rewrite ht /=.
Qed.

(* constant-time ---single step *) 
Definition constant_time (env: env_t) (s1 s2: asm_state) :=
forall c code s1' s2' l1 l2,
state_equiv c s1 s2 env ->
asmsem1 code s1 l1 s1' ->
asmsem1 code s2 l2 s2' ->
l1 = l2.

Lemma Public_only_less_than_Public : forall t, (t <= Public)%CMP -> t = Public.
Proof.
move=> t ht. by case: t ht=> //=.
Qed.

Lemma state_equiv_env_env' : forall c rho s1 s2 env env',
state_equiv rho s1 s2 env ->
valid_valuation c rho ->
le_env c env env' ->
state_equiv rho s1 s2 env'. 
Proof.
move=> c rho [] m1 fn1 code1 ip1 [] m2 fn2 code2 ip2 env env' hequiv hvalid hle.
case: hequiv=> /= hcode hpc hreg hregx hxreg hflag hmem; subst.
constructor; auto; rewrite /=; subst.
+ move=> r l ws hregty hrho.
  rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hr r)=> /= hle. rewrite hregty /= in hle. rewrite /le_ws /= in hle.
  case: hle=> /andP [/= hle hsz]. 
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_reg env r).1 l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_reg env r = ((e_reg env r).1, (e_reg env r).2). + by case: (e_reg env r)=> //=.
  move: (hreg r (e_reg env r).1 (e_reg env r).2 henv hpub)=> htenv. 
  by have := zero_extend_small_size hsz htenv.
+ move=> r l ws hregxty hrho.
  rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hrx r)=> /= hle. rewrite hregxty /= in hle. rewrite /le_ws /= in hle.
  case: hle=> /andP [/= hle hsz]. 
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_regx env r).1 l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_regx env r = ((e_regx env r).1, (e_regx env r).2). + by case: (e_regx env r)=> //=.
  move: (hregx r (e_regx env r).1 (e_regx env r).2 henv hpub)=> htenv. 
  by have := zero_extend_small_size hsz htenv.
+ move=> r l ws hxregty hrho.
  rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hxr r)=> /= hle. rewrite hxregty /= in hle. rewrite /le_ws /= in hle.
  case: hle=> /andP [/= hle hsz]. 
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_xreg env r).1 l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_xreg env r = ((e_xreg env r).1, (e_xreg env r).2). + by case: (e_xreg env r)=> //=.
  move: (hxreg r (e_xreg env r).1 (e_xreg env r).2 henv hpub)=> htenv. 
  by have := zero_extend_small_size hsz htenv.
+ move=> f l hfty hrho. rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hf f)=> /= hle. rewrite hfty /= in hle. rewrite /le_ws /= in hle.
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_flag env f) l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_flag env f = e_flag env f. + by auto. 
  by move: (hflag f (e_flag env f) henv hpub).
move=> pt l adr vp pts hwvp hvp hpty hrho i hi.
rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
move: (hm pt)=> /= hle. rewrite hpty /= in hle. rewrite /le_ws /= in hle.
inversion hvalid. case: H0=> hsecret hl. move: (hl (get_pt env pt) l hle)=> /= hl'.
rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
have henv : get_pt env pt = get_pt env pt. + by auto.
by move: (hmem pt (get_pt env pt) adr vp pts hwvp hvp henv hpub i hi).
Qed.

(* Type preserves state equivalence *) 
Lemma type_prev_state_equivalence : forall Env env env' rho s1 s2 c P Pt_info pts s1' s2' l1 l2, 
wt_code c pts Env Pt_info s1.(asm_c) ->
oseq.onth Env s1.(asm_ip) = Some env -> 
valid_valuation c rho ->
state_equiv rho s1 s2 env ->
asmsem1 P s1 l1 s1' ->
asmsem1 P s2 l2 s2' ->
oseq.onth Env s1'.(asm_ip) = Some env' ->
state_equiv rho s1' s2' env'.
Proof.
move=> Env env env' rho [] /= m1 fn1 code1 pc1 [] m2 fn2 code2 pc2 c P Pt_info pts s1' s2' l1 l2 hwt hpcenv hvalid hequiv.
have hequivcopy := hequiv. move: hequiv.
move=> [] /= hcode hpc hreg hregx hxreg hflag hmem hstep1 hstep2 hpcenv'; subst.
rewrite /wt_code /= in hwt.
move: (hwt pc2)=> /= hwtpc2. 
have hpc : pc2 < size code2. + admit. 
move: (hwtpc2 hpc)=> {hwtpc2} hwtpc2.
move: env env' hpcenv hpcenv' hreg hregx hxreg hflag hmem hequivcopy.
case: hwtpc2.
(* AsmOp *)
+ admit.
(* ALIGN *)
+ move=> env env' hpci hpcenv hpcenv' hle. rewrite hpcenv /=.
  move=> env1 env2 [] henv; subst. move=> hpcenv'' hreg hregx hxreg hflag hmem hequivcopy; subst.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval /= hpci /= in H0 H1.
  case: H0=> h h'; case: H1=> h'' h'''; subst.
  constructor; auto.
  + move=> r l ws hregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hreg' r l ws hregty hrho).
  + move=> r l ws hregxty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hregx' r l ws hregxty hrho).
  + move=> r l ws hxregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hxreg' r l ws hxregty hrho).
  + move=> f l hfty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hflag' f l hfty hrho).
  move=> pt l adr vp pts' hwvp hvp hpt hrho i hi. rewrite /= in hpcenv''. 
  rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
  have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
  case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
  by move: (hmem' pt l adr vp pts' hwvp hvp hpt hrho i hi).
(* LABEL lbl *)
+ move=> env env' lbl hpci hpcenv hpcenv' hle. rewrite hpcenv /=.
  move=> env1 env2 [] henv; subst. move=> hpcenv'' hreg hregx hxreg hflag hmem hequivcopy; subst.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval /= hpci /= in H0 H1.
  case: H0=> h h'; case: H1=> h'' h'''; subst.
  constructor; auto.
  + move=> r l ws hregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hreg' r l ws hregty hrho).
  + move=> r l ws hregxty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hregx' r l ws hregxty hrho).
  + move=> r l ws hxregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hxreg' r l ws hxregty hrho).
  + move=> f l hfty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hflag' f l hfty hrho).
  move=> pt l adr vp pts' hwvp hvp hpt hrho i hi. rewrite /= in hpcenv''. 
  rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
  have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
  case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
  by move: (hmem' pt l adr vp pts' hwvp hvp hpt hrho i hi).
(* JMP (fn, lbl) *)
+ move=> env env' fn' lbl pc hpci hpcenv /eqP hfn.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval /= hpci /= in H0 H1; subst.
  case: (get_fundef (asm_funcs P) fn) H0 H1=> //= fundef /= H0 H1; subst.
  move: H0. t_xrbindP=> pc' hlb' /= hs1' hleak; subst. move: H1. t_xrbindP=> pc'' hlb'' /= hs2' hleak'; subst.
  rewrite hlb' in hlb''. case: hlb''=> h; subst. 
  move=> hlbl hpcenv' hle env1 env2. rewrite hpcenv. move=> [] h; subst.   
  move=> hpcenv'' hreg hregx hxreg hflag hmem hequivcopy; subst.
  constructor; auto; subst.
  + move=> r l ws hregty hrho /=. admit.
  + admit.
  + admit.
  + admit.
  admit. 
(* JCC lbl ct *)
+ move=> env envf envt lbl ip ct hpci hpcenv hwct hlbl henvf henvt [hlef hlet] env1 env2.
  rewrite hpcenv. move=> [] h; subst. move=> hpcenv' hreg hregx hxreg hflag hmem hequivcopy.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval /= hpci /= in H0 H1; subst.
  rewrite /eval_Jcc /= in H0 H1. move: H0. t_xrbindP=> b hevalm pc hb hs1' hleak; subst.
  move: H1. t_xrbindP=> b' hevalm' pc' hb' hs2' hleak'; subst. rewrite /= in hpcenv'. 
Admitted.


(* Type preserves constant-time *) Print asm_state.
Lemma type_prev_constant_time : forall Env env rho s1 s2 c P Pt_info pts s1' s2' l1 l2, 
wt_code c pts Env Pt_info s1.(asm_c) ->
oseq.onth Env s1.(asm_ip) = Some env -> 
valid_valuation c rho ->
state_equiv rho s1 s2 env ->
asmsem1 P s1 l1 s1' ->
asmsem1 P s2 l2 s2' ->
l1 = l2 /\ state_equiv rho s1' s2' env.
Proof.
Admitted.


  






 













