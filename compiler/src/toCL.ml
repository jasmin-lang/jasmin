open Prog
open Utils

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

and pp_op2 fmt o e1 e2 = 
  assert false

and pp_opn fmt o es = 
  assert false 

and pp_expr fmt e = 
  match e with
  | Pconst z -> pp_print_i fmt z
  | Pvar x -> pp_gvar_i fmt x.gv
  | Pbool _b -> assert false 
  | Papp1(o, e) -> pp_op1 fmt o e
  | Papp2(o, e1, e2) -> pp_op2 fmt o e1 e2
  | PappN(o, es) -> pp_opn fmt o es
  | Parr_init _ | Pget _ | Psub _ | Pload _ -> assert false 
  | Pif _ -> assert false 

let pp_baseop fmt xs o es = 
  match o with
  | X86_instr_decl.MOV ws -> 
    Format.fprintf fmt "mov %a%a %a%a"
      pp_lval (List.nth xs 0)
      pp_uint ws
      pp_expr (List.nth es 0)
      pp_uint ws


  (* | MOVSX of wsize * wsize *)
  | MOVZX (ws1, ws2) -> 
    Format.fprintf fmt "cast %a%a %a%a"
      pp_lval (List.nth xs 0)
      pp_uint ws1
      pp_expr (List.nth es 0)
      pp_uint ws2

  (*
  | CMOVcc of wsize *)
  | ADD ws ->
      Format.fprintf fmt "adds %a%a %a%a %a%a %a%a"
         pp_lval (List.nth xs 1) pp_bool ()
         pp_lval (List.nth xs 5) pp_uint ws
         pp_expr (List.nth es 0) pp_uint ws
         pp_expr (List.nth es 1) pp_uint ws




      
(*  | SUB of wsize
  | MUL of wsize
  | IMUL of wsize
*)
  | IMULr ws ->
     Format.fprintf fmt "mull dontcare %a%a %a%a %a%a"
         pp_lval (List.nth xs 5) pp_uint ws
         pp_expr (List.nth es 0) pp_uint ws
         pp_expr (List.nth es 1) pp_uint ws
  
(* of wsize
  | IMULri of wsize
  | DIV of wsize
  | IDIV of wsize
  | CQO of wsize *)
  | ADC ws ->
    Format.fprintf fmt "adcs %a%a %a%a %a%a %a%a %a%a"
      pp_lval (List.nth xs 1) pp_bool ()
      pp_lval (List.nth xs 5) pp_uint ws
      pp_expr (List.nth es 0) pp_uint ws
      pp_expr (List.nth es 1) pp_uint ws
      pp_expr (List.nth es 2) pp_bool ()

  | SBB ws ->
    Format.fprintf fmt "sbbs %a%a %a%a %a%a %a%a %a%a"
      pp_lval (List.nth xs 1) pp_bool ()
      pp_lval (List.nth xs 5) pp_uint ws
      pp_expr (List.nth es 0) pp_uint ws
      pp_expr (List.nth es 1) pp_uint ws
      pp_expr (List.nth es 2) pp_bool ()

      
(*  | NEG of wsize
  | INC of wsize
  | DEC of wsize
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
    Format.fprintf fmt "and %a%a %a%a %a%a"
      pp_lval (List.nth xs 5) pp_uint ws
      pp_expr (List.nth es 0) pp_uint ws
      pp_expr (List.nth es 1) pp_uint ws
      
(*  | ANDN of wsize
  | OR of wsize
  | XOR of wsize
  | NOT of wsize
  | ROR of wsize
  | ROL of wsize
  | RCR of wsize
  | RCL of wsize
  | SHL of wsize
  | SHR of wsize
  | SAL of wsize
  | SAR of wsize
  | SHLD of wsize
  | SHRD of wsize
  | MULX of wsize
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
  | VPAND of wsize
  | VPANDN of wsize
  | VPOR of wsize
  | VPXOR of wsize
  | VPADD of velem * wsize
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
  | _ -> assert false 

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

let pp_i fmt i = 
  match i.i_desc with
  | Cassert _e -> Format.fprintf fmt "assert true" (* FIXME *)
  | Csyscall _ | Cif _ | Cfor _ | Cwhile _ | Ccall _ -> assert false
  | Cassgn (x, _, _, e) -> 
      Format.fprintf fmt "@[<h>mov %a %a@]" pp_lval x pp_expr e
  | Copn(xs, _, o, es) -> 
      pp_sopn fmt xs o es 

let pp_c fmt c = 
  Format.fprintf fmt "@[<v>%a;@]"
    (pp_list ";@ " pp_i) c


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
  
let pp_fun fmt fd = 
  Format.fprintf fmt "@[<v>proc main(@[<hov>%a;@ %a@]) = @ %a@ @ %a@ @ %a@]"
    pp_args fd.f_args
    pp_res  fd.f_ret
    pp_pre ()
    pp_c fd.f_body
    pp_post ()


  

  
