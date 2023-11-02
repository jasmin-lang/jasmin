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
  Format.fprintf fmt "%s_%s" (unsharp x.v_name) (string_of_uid x.v_id)

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
  | MULX_lo_hi ws ->
     Format.fprintf fmt "mull %a%a %a%a %a %a"
       pp_lval (List.nth xs 1) pp_uint ws
       pp_lval (List.nth xs 0) pp_uint ws
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
 | Ox86MULX ws ->
     Format.fprintf fmt "mull %a%a %a%a %a %a"
       pp_lval (List.nth xs 0) pp_uint ws
       pp_lval (List.nth xs 1) pp_uint ws
       pp_expr (List.nth es 0)
       pp_expr (List.nth es 1) 
 | Ox86MULX_hi ws -> assert false 
 | Ox86SLHinit | Ox86SLHupdate | Ox86SLHmove | Ox86SLHprotect _ -> assert false 

let pp_ext_op fmt xs o es =
  match o with
  | Arch_extra.BaseOp (_, o) -> pp_baseop fmt xs o es 
  | Arch_extra.ExtOp o -> pp_extop fmt xs o es 

let pp_sopn fmt xs o es = 
  match o with
  | Sopn.Opseudo_op _ -> assert false 
  | Sopn.Oslh _ -> assert false
  | Sopn.Oasm o -> pp_ext_op fmt xs o es 

let pp_i pd asmOp fmt i = 
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
          (Printer.pp_instr ~debug:true pd asmOp) i

let pp_c pd asmOp fmt c = 
  Format.fprintf fmt "@[<v>%a;@]"
    (pp_list ";@ " (pp_i pd asmOp)) c


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
  
let pp_fun pd asmOp fmt fd = 
  Format.fprintf fmt "@[<v>proc main(@[<hov>%a;@ %a@]) = @ %a@ @ %a@ @ %a@]"
    pp_args fd.f_args
    pp_res  fd.f_ret
    pp_pre ()
    (pp_c pd asmOp) fd.f_body
    pp_post ()


(*
let extract (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) prog cprog tokeep =

  let p = Compile.compile_CL (module Arch) cprog tokeep in
  List.iter (pp_fun Arch.reg_size Arch.asmOp   
*)

 
