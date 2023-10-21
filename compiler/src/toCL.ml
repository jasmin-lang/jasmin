open Allocation
open Arch_extra
open Arch_params
open Array_copy
open Array_expansion
open Array_init
open Compiler_util
open Dead_calls
open Dead_code
open Eqtype
open Expr
open Inline
open Lowering
open MakeReferenceArguments
open Propagate_inline
open Remove_globals
open Utils0
open Compiler
open Utils
open Prog
open Glob_options
open Utils



(* Language intermédiaire pour jasin: permet de d'écrire le comportement de chaque instruction et de générer
   des instruction pour une nouvelle cible


Jasmin arch -- compile_CL --> Jasmin arch  -- compile_low -->  Jasmin low --> cryptoline
                                                                    |
                                                                    |
                                                                  bit dependency 

- Semantique en Coq.
- Semantique en EC.
- Semantique en cryptoline.
- Semantique en bit dep


   Défintion soit par type dépendent/ soit par une fonction de type checking pour vérifier que l'on une
   expression low bien définie
   
low: 
  | Map2 of nat * wsize * wsize 
  | Add of wsize 
  | Var of name 
  | App of low * low list
  | Fun of name * ty * expr 
 
VPADD -> Fun "x" u64 (Fun "y" u64  (App (Map2 4 u64 u64, [:: Add u64; Var x; Var y])))

x y 
(xh,xl) = split x;
(xhh,xhl) = split xh;
(xlh,xll) = split xl;
(yh,yl) = split y;
(yhh,yhl) = split yh;
(ylh,yll) = split yl;
zhh = + ;
...
merge
   merge

wt low type 

semi_low low rho (wt low type) : semi_type type =
  | Fun n ty low' => fun (x: ty) => semi_low low ([n, x]) 
  | Var n => rho n


  | Map2 

wt_low : e 

  map2 4 u64 u64 (add sv) x y)

low : Inductif 
      datatype


arm_ADD_semi : w32 -> w32 -> w32

arm_ADD_low : low 

semi_low arm_ADD_low ... : w32 -> w32 -> w32

 {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: E 1; E 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: E 0 ];
      id_semi := arm_ADD_semi;   // low  
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}


id_semi instr ~ semi_low (id_low instr)

op -> 
      64 256
VPADD sv sr x y -> 
   map2 4 u64 u64 (add sv) x y)

   map2 4 u64 u32 (addsv) x y)
   
+ - mull mulh mul mod div xor and 
pack  
unpack 
map 
map2 
 

low:  -> cryptoline
      -> Coq 
      -> EC
 
x = y +4u64 z;   --> x = #VPADD_4_64(y, z);
x = #VPADD_4_64(y, z);

   
*)






(*
 Add to pexp contifier
   
big_rec [m..n[ (add: t-> t-> t) (f : int -> t) (x:t) : t 

big_rec [m..m[ add f x = x 
big_rec [m..n[ add f x = big [m+1 ..n[ add (add x (f m)) f


sum 
all and 
exists or 



big (add, zero) mn f = big_rec mn add f zero.

Inductive aexpr : Type :=
| Pconst :> Z -> aexpr
| Pbool  :> bool -> aexpr
| Pvar   :> gvar -> aexpr
| Pget   : arr_access -> wsize -> gvar -> aexpr -> aexpr
| Psub   : arr_access -> wsize -> positive -> gvar -> aexpr -> aexpr 
| Papp1  : sop1 -> aexpr -> aexpr
| Papp2  : sop2 -> aexpr -> aexpr -> aexpr
| PappN of opN & seq aexpr
| Pif    : stype -> aexpr -> aexpr -> aexpr -> aexpr
(* *)
| Pfvar : fvar (peut-être gvar)-> aexpr
| Big_rec of (n:eassert) (m:eassert) binop (i:fvar) (fbody:eassert) (x:eassert)

to_aexpr : pexpr -> aexpr
sem_pexpr 

forall e, sem_pexpr e = sem_aexpr (to_aexpr e) [::]

sem_pexpr rho

   [::]

x = y + z;
x = ADD(y, z);

sem_pexpr : state -> pexpr -> exec value
sem_aexpr : state -> list (fvar * value) -> aexpr -> exec value


sum i in [0..] 0 (fun i -> ...)

*)


let unsharp = String.map (fun c -> if c = '#' then '_' else c) 

let pp_var fmt x = 
  Format.fprintf fmt "%s_%i" (unsharp x.v_name) (int_of_uid x.v_id)

let pp_gvar_i fmt x = 
  pp_var fmt (L.unloc x)

let pp_lval fmt x = 
  match x with
  | Lvar x -> pp_gvar_i fmt x
  | Lnone _ -> Format.fprintf fmt "NONE____" 
  | Lmem _ | Laset _ | Lasub _ -> assert false 

let pp_print_i fmt z = 
  if Z.leq Z.zero z then Z.pp_print fmt z 
  else Format.fprintf fmt "(%a)" Z.pp_print z

let pp_bool fmt () =
  Format.fprintf fmt "@@uint1" 

let pp_uint fmt ws =
  Format.fprintf fmt "@@uint%i" (int_of_ws ws)

let pp_sint fmt ws =
  Format.fprintf fmt "@@sint%i" (int_of_ws ws)

let pp_bw fmt t =
  Format.fprintf fmt "@@%i" (int_of_ws t)

let pp_sign t =
  match t with
  | Wsize.Signed -> "s"
  | Unsigned -> "u"

let pp_int fmt s ws =
  Format.fprintf fmt "@@%sint%i" (pp_sign s) (int_of_ws ws)

let rec pp_op1 fmt o e = 
  match o with 
  | Expr.Oword_of_int ws -> 
    Format.fprintf fmt "%a" pp_expr e
  | Oint_of_word _ -> assert false 
  | Osignext _ -> assert false 
  | Ozeroext _ -> assert false 
  | Onot -> assert false 
  | Olnot _ -> assert false 
  | Oneg _ -> assert false

and pp_rop1 fmt o e = 
  match o with 
  | Expr.Oword_of_int ws -> pp_rexpr fmt (e, (Some ws))
  | Oint_of_word _ -> assert false 
  | Osignext _ -> assert false 
  | Ozeroext _ -> assert false 
  | Onot -> assert false 
  | Olnot _ -> assert false 
  | Oneg _ -> assert false 

and pp_op2 fmt o e1 e2 =
  match o with
  | Obeq -> assert false
  | Oand ->
      Format.fprintf fmt "and [%a, %a]" pp_rexpr (e1, None) pp_rexpr (e2, None)
  | Oor ->
      Format.fprintf fmt "or [%a, %a]" pp_rexpr (e1, None) pp_rexpr (e2, None)
  | Oadd Op_int
  | Omul Op_int
  | Osub Op_int
  | Odiv Cmp_int | Omod Cmp_int
  | Olsl Op_int | Oasr Op_int -> assert false
  | Oadd (Op_w ws) -> Format.fprintf fmt "(%a + %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Omul (Op_w ws) -> Format.fprintf fmt "%a * %a" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Osub (Op_w ws) -> Format.fprintf fmt "(%a - %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Odiv (Cmp_w (_, s)) -> assert false
  | Omod (Cmp_w (s, ws)) ->
     Format.fprintf fmt "%smod %a %a" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Oland ws -> Format.fprintf fmt "(%a & %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Olor ws -> Format.fprintf fmt "(%a | %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Olxor ws -> Format.fprintf fmt "(%a ^ %a)" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Ovadd (_, s) | Ovsub (_, s) | Ovmul (_, s) -> assert false
  | Olsr s -> Format.fprintf fmt "shr %a %a" pp_rexpr (e1, Some s) pp_rexpr (e2, Some s)
  | Olsl (Op_w s) -> Format.fprintf fmt "shl %a %a" pp_rexpr (e1, Some s) pp_rexpr (e2, Some s)
  | Oasr (Op_w s) -> Format.fprintf fmt "sar %a %a" pp_rexpr (e1, Some s) pp_rexpr (e2, Some s)
  | Oror s | Orol s | Ovlsr (_, s) | Ovlsl (_, s) | Ovasr (_, s) -> assert false
  | Oeq Op_int | Oneq Op_int
  | Olt Cmp_int | Ole Cmp_int
  | Ogt Cmp_int | Oge Cmp_int -> assert false
  | Oeq (Op_w ws) ->
     Format.fprintf fmt "eq %a %a" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Oneq (Op_w ws) ->
     Format.fprintf fmt "neg eq %a %a" pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Olt (Cmp_w (s,ws)) ->
     Format.fprintf fmt "%slt %a %a" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Ole (Cmp_w (s,ws)) ->
     Format.fprintf fmt "%sle %a %a" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Ogt (Cmp_w (s,ws)) ->
     Format.fprintf fmt "%sgt %a %a" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)
  | Oge (Cmp_w (s,ws)) ->
     Format.fprintf fmt "%sge %a %a" (pp_sign s) pp_rexpr (e1, Some ws) pp_rexpr (e2, Some ws)


and pp_opn fmt o es = 
  assert false 

and pp_rexpr fmt (e,ws) =
  match e with
  | Pconst z -> Format.fprintf fmt "%a%a" pp_print_i z pp_bw (oget ws)
  | Pvar x -> pp_gvar_i fmt x.gv
  | Pbool b -> Format.fprintf fmt "%b" b
  | Papp1(o, e) -> pp_rop1 fmt o e
  | Papp2(o, e1, e2) -> pp_op2 fmt o e1 e2
  | PappN(o, es) -> pp_opn fmt o es
  | _ -> assert false

and pp_expr fmt e = 
  match e with
  | Pconst z -> pp_print_i fmt z
  | Pvar x -> pp_gvar_i fmt x.gv
  | Pbool _b -> assert false 
  | Papp1(o, e) -> pp_op1 fmt o e
  | Papp2(o, e1, e2) -> pp_op2 fmt o e1 e2
  | PappN(o, es) -> pp_opn fmt o es
  | Parr_init _ -> assert false
  | Pget _ -> assert false
  | Psub _ -> assert false
  | Pload _ -> assert false 
  | Pif _ -> assert false

and pp_pred fmt e =
  pp_rexpr fmt (e, None)

and pp_cast fmt (ws_d, e) =
  let ws_s = (match e with
              | Pvar x -> ws_of_ty (L.unloc x.gv).v_ty
              | Pconst z -> ws_d
              | _ -> ws_d (* FIXME: fail?? *)
             ) in  
  if ws_d != ws_s then
    Format.fprintf fmt "cast %a%a %a;\n"
    pp_expr e pp_uint ws_d
    pp_expr e
  else Format.fprintf fmt ""

exception NoTranslation

let pp_baseop fmt xs o es =
  match o with
  | X86_instr_decl.MOV ws ->
     (match (List.nth es 0) with
      | Pvar x ->
         let ws_x = ws_of_ty (L.unloc x.gv).v_ty in
         if ws_x != ws (* implicit cast *)
         then Format.fprintf fmt "cast %a%a %a"
                pp_lval (List.nth xs 0)
                pp_uint ws
                pp_expr (List.nth es 0)
         else Format.fprintf fmt "mov %a %a"
               pp_lval (List.nth xs 0)
               pp_expr (List.nth es 0)
      | _ -> Format.fprintf fmt "mov %a %a"
               pp_lval (List.nth xs 0)
               pp_expr (List.nth es 0)
     )

  | MOVSX (ws1, ws2) ->
     Format.fprintf fmt "cast %a%a %a"
       pp_lval (List.nth xs 0)
       pp_uint ws1
       pp_expr (List.nth es 0)

  | MOVZX (ws1, ws2) -> 
    Format.fprintf fmt "cast %a%a %a"
      pp_lval (List.nth xs 0)
      pp_uint ws1
      pp_expr (List.nth es 0)

  | CMOVcc ws ->
     Format.fprintf fmt "cmov %a %a %a %a"
       pp_lval (List.nth xs 0)
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)
       pp_expr (List.nth es 2)

  | ADD ws ->
     Format.fprintf fmt "%a%aadds %a%a %a %a %a"
       pp_cast (ws, (List.nth es 0))
       pp_cast (ws, (List.nth es 1))
       pp_lval (List.nth xs 1) pp_bool ()
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)

  | SUB ws ->
     Format.fprintf fmt "%a%asubb %a%a %a %a %a"
       pp_cast (ws, (List.nth es 0))
       pp_cast (ws, (List.nth es 1))
       pp_lval (List.nth xs 1) pp_bool ()
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)
(*
  | MUL ws ->
     Format.fprintf fmt "umull"
  | IMUL of wsize
*)
  | IMULr ws ->
     Format.fprintf fmt "mull dontcare %a%a %a %a"
       pp_lval (List.nth xs 5) pp_uint ws
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)
  
  | IMULri ws ->
     Format.fprintf fmt "mull dontcare %a%a %a %a%a"
       pp_lval (List.nth xs 5) pp_uint ws
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1) pp_uint ws

  (*
  | DIV of wsize
  | IDIV of wsize
  | CQO of wsize
   *)
  | ADC ws ->
    Format.fprintf fmt "adcs %a%a %a %a %a %a%a"
      pp_lval (List.nth xs 1) pp_bool ()
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)
      pp_expr (List.nth es 2) pp_bool ()

  | SBB ws ->
    Format.fprintf fmt "sbbs %a%a %a %a %a %a%a"
      pp_lval (List.nth xs 1) pp_bool ()
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)
      pp_expr (List.nth es 2) pp_bool ()

  | NEG ws ->
     Format.fprintf fmt "sub %a %a %a"
       pp_lval (List.nth xs 4)
       pp_print_i (Z.of_int 0)
       pp_expr (List.nth es 0)

  | INC ws ->
     Format.fprintf fmt "add %a%a %a%a %a%a"
       pp_lval (List.nth xs 4) pp_uint ws
       pp_expr (List.nth es 0) pp_uint ws
       pp_print_i (Z.of_int 1) pp_uint ws

  | DEC ws ->
     Format.fprintf fmt "sub %a%a %a%a %a%a"
       pp_lval (List.nth xs 4) pp_uint ws
       pp_expr (List.nth es 0) pp_uint ws
       pp_print_i (Z.of_int 1) pp_uint ws
(*
  | LZCNT of wsize
  | SETcc
  | BT of wsize
  | CLC
  | STC
  | LEA of wsize
  | TEST of wsize
  | CMP of wsize
*)
  | AND ws ->
    Format.fprintf fmt "and %a %a %a"
      pp_lval (List.nth xs 5)
      pp_expr (List.nth es 0)
      pp_expr (List.nth es 1)
      
  | ANDN ws ->
     Format.fprintf fmt "not %a %a;\nand %a %a %a"
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 0)
       pp_lval (List.nth xs 5)
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 1)

  | OR ws ->
     Format.fprintf fmt "or %a %a %a"
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)

  | XOR ws ->
     Format.fprintf fmt "xor %a %a %a"
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)

  | NOT ws ->
     Format.fprintf fmt "not %a%a %a"
       pp_lval (List.nth xs 5) pp_uint ws
       pp_expr (List.nth es 0)

  (* | ROR ws -> *)
  (*    Format.fprintf fmt "ror %a%a %a%a %a@@uint8" *)
  (*      pp_lval (List.nth xs 5) pp_uint ws *)
  (*      pp_expr (List.nth es 0) pp_uint ws *)
  (*      pp_expr (List.nth es 1) *)

  (* | ROL ws -> *)
  (*    Format.fprintf fmt "rol %a%a %a%a %a@@uint8" *)
  (*      pp_lval (List.nth xs 5) pp_uint ws *)
  (*      pp_expr (List.nth es 0) pp_uint ws *)
  (*      pp_expr (List.nth es 1) *)
(*
  | RCR of wsize
  | RCL of wsize
 *)

  | SHL ws ->
     Format.fprintf fmt "shl %a %a %a"
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)

  | SHR ws ->
     Format.fprintf fmt "shr %a %a %a"
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)

  | SAL ws ->
     Format.fprintf fmt "shl %a %a %a"
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)

  | SAR ws ->
     Format.fprintf fmt "sar %a %a %a"
       pp_lval (List.nth xs 5)
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)
(*
  | SHLD of wsize
  | SHRD of wsize
 *)
  | MULX ws ->
     Format.fprintf fmt "mull %a%a %a%a %a %a"
       pp_lval (List.nth xs 0) pp_uint ws
       pp_lval (List.nth xs 1) pp_uint ws
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)
(*
  | ADCX of wsize
  | ADOX of wsize
  | BSWAP of wsize
  | POPCNT of wsize
  | PEXT of wsize
  | PDEP of wsize
  | MOVX of wsize
  | MOVD of wsize
  | MOVV of wsize
  | VMOV of wsize
  | VMOVDQA of wsize
  | VMOVDQU of wsize
  | VPMOVSX of velem * wsize * velem * wsize
  | VPMOVZX of velem * wsize * velem * wsize
 *)
  | VPAND ws ->
     Format.fprintf fmt "and %a%a %a %a"
       pp_lval (List.nth xs 0) pp_uint ws
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1)

  | VPANDN ws ->
     Format.fprintf fmt "not %a%a %a%a;\nand %a%a %a%a %a%a"
       pp_lval (List.nth xs 5) pp_uint ws
       pp_expr (List.nth es 0) pp_uint ws
       pp_lval (List.nth xs 5) pp_uint ws
       pp_lval (List.nth xs 5) pp_uint ws
       pp_expr (List.nth es 1) pp_uint ws

  | VPOR ws ->
     Format.fprintf fmt "or %a%a %a%a %a%a"
       pp_lval (List.nth xs 0) pp_uint ws
       pp_expr (List.nth es 0) pp_uint ws
       pp_expr (List.nth es 1) pp_uint ws

  | VPXOR ws ->
     Format.fprintf fmt "xor %a%a %a%a %a%a"
       pp_lval (List.nth xs 0) pp_uint ws
       pp_expr (List.nth es 0) pp_uint ws
       pp_expr (List.nth es 1) pp_uint ws

  (*
  | VPADD (ve,ws) ->
     let ve0 = Word0.nat_of_wsize (Wsize.wsize_of_velem ve) in
     let v1 = Word0.split_vec ws ve0 (List.nth es 0) in
     let v2 = Word0.split_vec ws ve0 (List.nth es 1) in
     Format.fprintf fmt "add %a%a %a%a %a%a"
       pp_lval (List.nth xs 0) pp_uint ws
       pp_expr (List.nth es 0) pp_uint ws
       pp_expr (List.nth es 1) pp_uint ws

  | VPSUB of velem * wsize
  | VPAVG of velem * wsize
  | VPMULL of velem * wsize
  | VPMULH of velem * wsize
  | VPMULHU of velem * wsize
  | VPMULHRS of velem * wsize
  | VPMUL of wsize
  | VPMULU of wsize
  | VPEXTR of wsize
  | VPINSR of velem
  | VPSLL of velem * wsize
  | VPSRL of velem * wsize
  | VPSRA of velem * wsize
  | VPSLLV of velem * wsize
  | VPSRLV of velem * wsize
  | VPSLLDQ of wsize
  | VPSRLDQ of wsize
  | VPSHUFB of wsize
  | VPSHUFD of wsize
  | VPSHUFHW of wsize
  | VPSHUFLW of wsize
  | VPBLEND of velem * wsize
  | VPBLENDVB of wsize
  | VPACKUS of velem * wsize
  | VPACKSS of velem * wsize
  | VSHUFPS of wsize
  | VPBROADCAST of velem * wsize
  | VMOVSHDUP of wsize
  | VMOVSLDUP of wsize
  | VPALIGNR of wsize
  | VBROADCASTI128
  | VPUNPCKH of velem * wsize
  | VPUNPCKL of velem * wsize
  | VEXTRACTI128
  | VINSERTI128
  | VPERM2I128
  | VPERMD
  | VPERMQ
  | VPMOVMSKB of wsize * wsize
  | VPCMPEQ of velem * wsize
  | VPCMPGT of velem * wsize
  | VPMADDUBSW of wsize
  | VPMADDWD of wsize
  | VMOVLPD
  | VMOVHPD
  | VPMINU of velem * wsize
  | VPMINS of velem * wsize
  | VPMAXU of velem * wsize
  | VPMAXS of velem * wsize
  | VPTEST of wsize
  | CLFLUSH
  | LFENCE
  | MFENCE
  | SFENCE
  | RDTSC of wsize
  | RDTSCP of wsize
  | AESDEC
  | VAESDEC
  | AESDECLAST
  | VAESDECLAST
  | AESENC
  | VAESENC
  | AESENCLAST
  | VAESENCLAST
  | AESIMC
  | VAESIMC
  | AESKEYGENASSIST
  | VAESKEYGENASSIST *)
  | _ -> raise NoTranslation 


let pp_extop fmt xs o es = 
  match o with
  | X86_extra.Oset0 ws -> 
      (* FIXME this work for size less than 64 *)
      Format.fprintf fmt "mov %a 0%a"
        pp_lval (List.nth xs 5)
        pp_uint ws
  | Oconcat128 -> assert false
  | Ox86MOVZX32 -> 
      Format.fprintf fmt "cast %a@@uint64 %a@@uint32"
        pp_lval (List.nth xs 0) 
        pp_expr (List.nth es 0) 
 

let pp_ext_op fmt xs o es =
  match o with
  | Arch_extra.BaseOp (_, o) -> pp_baseop fmt xs o es 
  | Arch_extra.ExtOp o -> pp_extop fmt xs o es 

let pp_sopn fmt xs o es = 
  match o with
  | Sopn.Ocopy _ -> assert false 
  | Sopn.Onop    -> assert false 
  | Sopn.Omulu _ws -> assert false 
  | Sopn.Oaddcarry _ws -> assert false 
  | Sopn.Osubcarry _ws -> assert false 
  | Sopn.Oasm o -> pp_ext_op fmt xs o es 

let pp_i asmOp fmt i = 
  match i.i_desc with
  | Cassert (t, p, e) ->
     let efmt = (match p with
                 | Expr.Cas -> format_of_string "%s true && %a"
                 | Expr.Smt -> format_of_string "%s %a && true"
                ) in
     (match t with
      | Expr.Assert -> Format.fprintf fmt efmt "assert" pp_pred e
      | Expr.Assume -> Format.fprintf fmt efmt "assume" pp_pred e (* FIXME: check syntax *)
      | Expr.Cut -> Format.fprintf fmt efmt "cut" pp_pred e (* FIXME: check syntax *)
     )
  | Csyscall _ | Cif _ | Cfor _ | Cwhile _ | Ccall _ -> assert false
  | Cassgn (x, _, _, e) -> 
      Format.fprintf fmt "@[<h>mov %a %a@]" pp_lval x pp_expr e
  | Copn(xs, _, o, es) -> 
      try 
        pp_sopn fmt xs o es 
      with NoTranslation ->
       Format.eprintf "No Translation for: %a@."
          (Printer.pp_instr ~debug:true asmOp) i

let pp_c asmOp fmt c = 
  Format.fprintf fmt "@[<v>%a;@]"
    (pp_list ";@ " (pp_i asmOp)) c


let pp_pre fmt fd = 
  Format.fprintf fmt "@[<v>{@   true@   &&@   true@ }@]"   

let pp_post fmt fd = 
  pp_pre fmt fd 

let pp_ty fmt ty =
  match ty with
  | Bty Bool -> Format.fprintf fmt "uint1"
  | Bty Int -> assert false
  | Bty (U ws) -> Format.fprintf fmt "uint%i" (int_of_ws ws)
  | Arr _ -> assert false

let pp_args fmt xs = 
  (pp_list ",@ " 
     (fun fmt x -> Format.fprintf fmt "%a %a"
                     pp_ty x.v_ty pp_var x)) fmt xs

let pp_res fmt xs = 
  pp_args fmt (List.map L.unloc xs)
  
let pp_fun asmOp fmt fd = 
  Format.fprintf fmt "@[<v>proc main(@[<hov>%a;@ %a@]) = @ %a@ @ %a@ @ %a@]"
    pp_args fd.f_args
    pp_res  fd.f_ret
    pp_pre ()
    (pp_c asmOp) fd.f_body
    pp_post ()


module Scmp = struct
  type t = string
  let compare = compare
end

module Ss = Set.Make(Scmp)

let filter prog tbl cl_list =
  let rec used_func f =
    let (_,fundef) = f in
    used_func_c Ss.empty Linear.(fundef.lfd_body)

  and used_func_c used c =
    List.fold_left used_func_i used c

  and used_func_i used i =
    match i.li_i with
    | Lcall (_,(f,_))   -> Ss.add (Conv.string_of_funname tbl f) used
    | _ -> used
  in

  let tokeep = ref (Ss.of_list cl_list) in
  let dofun f =
    let (name,_) = f in
    if Ss.mem (Conv.string_of_funname tbl name) !tokeep then
      (tokeep := Ss.union (used_func f) !tokeep; true)
    else false in
  let lp_funcs = List.rev (List.filter dofun Linear.(prog.lp_funcs)) in
  Linear.({prog with lp_funcs})

let rec warn_extra_i asmOp i =
  match i.i_desc with
  | Cassgn (_, tag, _, _) | Copn (_, tag, _, _) -> (
      match tag with
      | AT_rename ->
          warning ExtraAssignment i.i_loc
            "@[<v>extra assignment introduced:@;<0 2>%a@]"
            (Printer.pp_instr ~debug:false asmOp)
            i
      | AT_inline ->
          hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
            "@[<v>AT_inline flag remains in instruction:@;<0 2>@[%a@]@]"
            (Printer.pp_instr ~debug:false asmOp)
            i
      | _ -> ())
  | Cif (_, c1, c2) | Cwhile (_, c1, _, c2) ->
      List.iter (warn_extra_i asmOp) c1;
      List.iter (warn_extra_i asmOp) c2
  | Cfor _ ->
      hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
        "for loop remains"
  | Ccall _ | Csyscall _ | Cassert _ -> ()

let warn_extra_fd asmOp (_, fd) = List.iter (warn_extra_i asmOp) fd.f_body

let extract (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) visit_prog_after_pass fmt prog tbl cprog tokeep =

  let asmOp = Arch.asmOp in
  let asm_e = Arch.asm_e in
  let call_conv = Arch.call_conv in
  let p = (Expr.to_uprog asmOp cprog) in

    let module Regalloc = Regalloc.Regalloc (Arch) in
  let module StackAlloc = StackAlloc.StackAlloc (Arch) in
  let fdef_of_cufdef fn cfd = Conv.fdef_of_cufdef tbl (fn, cfd) in
  let cufdef_of_fdef fd = snd (Conv.cufdef_of_fdef tbl fd) in

  let apply msg trans fn cfd =
    if !debug then Format.eprintf "START %s@." msg;
    let fd = fdef_of_cufdef fn cfd in
    if !debug then Format.eprintf "back to ocaml@.";
    let fd = trans fd in
    cufdef_of_fdef fd
  in

  let translate_var = Conv.var_of_cvar tbl in

  let memory_analysis up : Compiler.stack_alloc_oracles =
    StackAlloc.memory_analysis
      (Printer.pp_err ~debug:!debug)
      ~debug:!debug tbl up
  in

  let saved_extra_free_registers : (L.i_loc -> var option) ref =
    ref (fun _ -> None)
  in

  let global_regalloc fds =
    if !debug then Format.eprintf "START regalloc@.";
    let fds = List.map (Conv.fdef_of_csfdef tbl) fds in

    CheckAnnot.check_stack_size fds;

    let fds, extra_free_registers =
      Regalloc.alloc_prog translate_var
        (fun _fd extra ->
          match extra.Expr.sf_save_stack with
          | Expr.SavedStackReg _ | Expr.SavedStackStk _ -> true
          | Expr.SavedStackNone -> false)
        fds
    in
    saved_extra_free_registers := extra_free_registers;
    let fds = List.map (fun (y, _, x) -> (y, x)) fds in
    let fds = List.map (Conv.csfdef_of_fdef tbl) fds in
    fds
  in

  let is_var_in_memory cv : bool =
    let v = Conv.vari_of_cvari tbl cv |> L.unloc in
    match v.v_kind with
    | Stack _ | Reg (_, Pointer _) | Global -> true
    | Const | Inline | Reg (_, Direct) -> false
  in

  let pp_cuprog s cp =
    Conv.prog_of_cuprog tbl cp |> visit_prog_after_pass ~debug:true s
  in

  let pp_csprog fmt cp =
    let p = Conv.prog_of_csprog tbl cp in
    Printer.pp_sprog ~debug:true tbl Arch.asmOp fmt p
  in

  let pp_linear fmt lp = PrintLinear.pp_prog Arch.asmOp tbl fmt lp in

  let rename_fd ii fn cfd =
    let ii, _ = ii in
    let doit fd =
      let fd = Subst.clone_func fd in
      Subst.extend_iinfo ii fd
    in
    apply "rename_fd" doit fn cfd
  in

  let expand_fd fn cfd =
    let fd = Conv.fdef_of_cufdef tbl (fn, cfd) in
    let vars, harrs = Array_expand.init_tbl fd in
    let cvar = Conv.cvar_of_var tbl in
    let vars = List.map cvar (Sv.elements vars) in
    let arrs = ref [] in
    let doarr x (ws, xs) =
      arrs :=
        Array_expansion.
          {
            vi_v = cvar x;
            vi_s = ws;
            vi_n =
              List.map (fun x -> (cvar x).Var0.Var.vname) (Array.to_list xs);
          }
        :: !arrs
    in
    Hv.iter doarr harrs;
    { Array_expansion.vars; arrs = !arrs }
  in

  let warning ii msg =
    (if not !Glob_options.lea then
     let loc, _ = ii in
     warning UseLea loc "%a" Printer.pp_warning_msg msg);
    ii
  in

  let inline_var x =
    let x = Conv.var_of_cvar tbl x in
    x.v_kind = Inline
  in

  let is_glob x =
    let x = Conv.var_of_cvar tbl x in
    x.v_kind = Global
  in

  let fresh_id _gd x =
    let x = Conv.var_of_cvar tbl x in
    let x' = Prog.V.clone x in
    let cx = Conv.cvar_of_var tbl x' in
    cx.Var0.Var.vname
  in

  let fresh_reg name ty =
    let name = Conv.string_of_string0 name in
    let ty = Conv.ty_of_cty ty in
    let p = Prog.V.mk name (Reg (Normal, Direct)) ty L._dummy [] in
    let cp = Conv.cvar_of_var tbl p in
    cp.Var0.Var.vname
  in

  let fresh_counter =
    let i = Prog.V.mk "i__copy" Inline tint L._dummy [] in
    let ci = Conv.cvar_of_var tbl i in
    ci.Var0.Var.vname
  in

  let split_live_ranges_fd fd = Regalloc.split_live_ranges fd in
  let renaming_fd fd = Regalloc.renaming fd in
  let remove_phi_nodes_fd fd = Regalloc.remove_phi_nodes fd in

  let removereturn sp =
    let fds, _data = Conv.prog_of_csprog tbl sp in
    let tokeep = RemoveUnusedResults.analyse Arch.aparams.ap_is_move_op fds in
    let tokeep fn = tokeep (Conv.fun_of_cfun tbl fn) in
    tokeep
  in

  let is_regx tbl x = is_regx (Conv.var_of_cvar tbl x) in

  let is_reg_ptr x =
    let x = Conv.var_of_cvar tbl x in
    is_reg_ptr_kind x.v_kind
  in

  let is_ptr x =
    let x = Conv.var_of_cvar tbl x in
    is_ptr x.v_kind
  in

  let is_reg_array x = is_reg_arr (Conv.var_of_cvar tbl x) in

  let warn_extra s p =
    if s = Compiler.DeadCode_RegAllocation then
      let fds, _ = Conv.prog_of_csprog tbl p in
      List.iter (warn_extra_fd Arch.asmOp) fds
  in

  let cparams =
    {
      Compiler.rename_fd;
      Compiler.expand_fd;
      Compiler.split_live_ranges_fd =
        apply "split live ranges" split_live_ranges_fd;
      Compiler.renaming_fd = apply "alloc inline assgn" renaming_fd;
      Compiler.remove_phi_nodes_fd =
        apply "remove phi nodes" remove_phi_nodes_fd;
      Compiler.stack_register_symbol =
        Var0.Var.vname (Conv.cvar_of_var tbl Arch.rsp_var);
      Compiler.global_static_data_symbol =
        Var0.Var.vname (Conv.cvar_of_var tbl Arch.rip);
      Compiler.stackalloc = memory_analysis;
      Compiler.removereturn;
      Compiler.regalloc = global_regalloc;
      Compiler.extra_free_registers =
        (fun ii ->
          let loc, _ = ii in
          !saved_extra_free_registers loc |> Option.map (Conv.cvar_of_var tbl));
      Compiler.lowering_vars = Arch.lowering_vars tbl;
      Compiler.is_var_in_memory;
      Compiler.print_uprog =
        (fun s p ->
          pp_cuprog s p;
          p);
      Compiler.print_sprog =
        (fun s p ->
          warn_extra s p;
          eprint s pp_csprog p;
          p);
      Compiler.print_linear =
        (fun s p ->
          eprint s pp_linear p;
          p);
      Compiler.warning;
      Compiler.inline_var;
      Compiler.lowering_opt = Arch.lowering_opt;
      Compiler.is_glob;
      Compiler.fresh_id;
      Compiler.fresh_counter;
      Compiler.fresh_reg;
      Compiler.fresh_reg_ptr = Conv.fresh_reg_ptr tbl;
      Compiler.is_reg_ptr;
      Compiler.is_ptr;
      Compiler.is_reg_array;
      Compiler.is_regx = is_regx tbl;
    }
  in

  let export_functions, subroutines =
    let conv fd = Conv.cfun_of_fun tbl fd.f_name in
    List.fold_right
      (fun fd ((e, i) as acc) ->
         match fd.f_cc with
         | Export -> (conv fd :: e, i)
         | Internal -> acc
         | Subroutine _ -> (e, conv fd :: i))
      (snd prog) ([], [])
  in

  let aparams = Arch.aparams in

  match compiler_first_part asm_e aparams cparams (Seq.cat export_functions subroutines) p with
  | Ok x ->
    (* let up = Conv.prog_of_cuprog tbl x in *)
    (* Printer.pp_prog ~debug:false asmOp fmt up; *)
    let ao = cparams.stackalloc (Obj.magic x) in
    (match check_no_ptr (Obj.magic export_functions) ao.ao_stack_alloc with
     | Ok _ ->
       (match Stack_alloc.alloc_prog (Arch_decl.arch_pd asm_e._asm._arch_decl) (asm_opI asm_e) true
                (aparams.ap_sap cparams.is_regx) cparams.fresh_reg
                cparams.global_static_data_symbol
                cparams.stack_register_symbol ao.ao_globals
                ao.ao_global_alloc ao.ao_stack_alloc (Obj.magic x) with
       | Ok x0 ->
         let ps = cparams.print_sprog StackAllocation x0 in
         (match compiler_third_part asm_e aparams cparams export_functions
                  (Obj.magic ps) with
         | Ok x1 ->
           (match compiler_back_end asm_e call_conv aparams cparams (Obj.magic export_functions) x1 with
            | Ok x ->
              let x = filter x tbl tokeep in
              PrintLinear.pp_prog asmOp tbl fmt x;
              Ok x
            | Error s -> Error s)
         | Error s -> Error s)
       | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s
