%{
open IL_Lang
open Core_kernel
open Arith

module P = ParserUtil
module L = Lexing

type instr_decl = Ins of instr | Decl of (string * ty) list

let fix_indexes (idxs,(cstart,cend)) =
  Std.List.filter_map idxs
    ~f:(function
          | Get i -> Some i
          | All -> let scnum = cstart.Lexing.pos_cnum + 1 in
                   let ecnum = cend.Lexing.pos_cnum + 1 in
                   let err = "range not allowed here" in
                   raise (ParserUtil.UParserError(scnum,ecnum,err)))

let pr_e_of_pr (pr,(cstart,cend)) =
  { pr with pr_idxs = fix_indexes (pr.pr_idxs,(cstart,cend)) }

let dest_e_of_dest (d,(cstart,cend))  =
  let pr = pr_e_of_pr (d.d_pr,(cstart,cend)) in
  { d_pr = pr; d_aidxs = fix_indexes (d.d_aidxs,(cstart,cend)) }

let src_e_of_src (s,(cstart,cend)) =
  match s with
  | Imm(i) -> Imm(i)
  | Src(d) -> Src(dest_e_of_dest (d,(cstart,cend)))

%}

/*======================================================================*/
/* Tokens */

%token EOF

%token LBRACK RBRACK LCBRACE RCBRACE LPAREN RPAREN
%token EQ
%token INEQ
%token PLUSEQ MINUSEQ BANDEQ
%token LEQ
%token LESS
%token GREATER
%token GEQ
%token SHREQ SHLEQ XOREQ
%token COLON
%token EQCALL

%token T_U64
%token T_BOOL

%token STAR
%token BAND
%token MINUS
%token PLUS
%token LAND
%token SEMICOLON
%token QUESTION
%token EXCL DOTDOT COMMA
(* %token PERCENT *)
%token SHR
%token SHL
%token XOR

%token REG
%token FLAG

%token FOR
%token IN
%token IF
%token ELSE
%token ELIF
%token TRUE
%token FALSE
%token EXTERN
%token FN
%token RETURN

%token <string> ID 
%token <int64>  INT

%left LAND
%nonassoc EXCL
%left MINUS PLUS
%left STAR

%type <IL_Lang.efun list> efuns

%start efuns

%%

(* -------------------------------------------------------------------- *)
(* Utility productions *)

%inline loc(X):
| x=X { (x, ($startpos,$endpos) ) }

(* -------------------------------------------------------------------- *)
(* Index expressions and conditions *)

%inline tuple(X):
| LPAREN l = separated_list(COMMA,X) RPAREN { l }
| l = separated_list(COMMA,X) { l }

%inline pbinop :
| PLUS    { Pplus }
| STAR    { Pmult }
| MINUS   { Pminus }

%inline pcondop :
| EQ      { Peq }
| INEQ    { Pineq }
| LESS    { Pless }
| LEQ     { Pleq }
| GREATER { Pgreater }
| GEQ     { Pgeq }

pexpr :
| s=ID                       { Pvar(s) }
| i=INT                      { Pconst(U64.of_int64 i) }
| e1=pexpr o=pbinop e2=pexpr { Pbinop(o,e1,e2) }
| LPAREN e1=pexpr RPAREN     { e1 }

pcond :
| TRUE                        { Ptrue }
| FALSE                       { Pnot(Ptrue) }
| EXCL c=pcond                { Pnot(c) }
| c1=pcond LAND c2=pcond      { Pand(c1,c2) }
| LPAREN c = pcond RPAREN     { c }
| c1=pexpr o=pcondop c2=pexpr { Pcond(o,c1,c2) }

pr_index :
| ce = pexpr
  { Get(ce) }
| DOTDOT
  { All }

%inline preg_nl :
| s=ID
    { { pr_name = s; pr_idxs = []; pr_loc = P.dummy_loc } }
| s=ID LESS pis = separated_list(COMMA,pr_index) GREATER
    { { pr_name = s; pr_idxs = pis; pr_loc = P.dummy_loc } }

%inline preg :
| lpr = loc(preg_nl)
    { let (pr,loc) = lpr in
      let loc =P.loc_of_lexing_loc loc in
      { pr with pr_loc = loc} }

%inline array_indexes :
| LBRACK pis = separated_list(COMMA,pr_index) RBRACK
    { pis }


(* -------------------------------------------------------------------- *)
(* Operators and assignments *)

src :
| r=preg arr=array_indexes?
    { Src({d_pr = r; d_aidxs = Option.value ~default:[] arr}) }
| i=INT
    { Imm(U64.of_int64 i) }

dest :
| r=preg arr=array_indexes?
    { { d_pr = r; d_aidxs = Option.value ~default:[] arr} }

cfin:
| PLUS  cf_in=loc(preg) { (`Add,cf_in) }
| MINUS cf_in=loc(preg) { (`Sub,cf_in) }

binop:
| PLUS  { `Plus }
| MINUS { `Minus }
| BAND  { `BAnd }
| SHR   { `Shift(Right) }
| SHL   { `Shift(Left) }
| XOR   { `Xor } 

%inline opeq:
| PLUSEQ  { `Add }
| MINUSEQ { `Sub }
| BANDEQ  { `And }
| SHREQ   { `Shift(Right) }
| SHLEQ   { `Shift(Left) }
| XOREQ   { `Xor } 

(* -------------------------------------------------------------------- *)
(* instructions *)

%inline cfout:
| r_cf_out=preg QUESTION { { d_pr = r_cf_out; d_aidxs = [] } }

%inline assgn_rhs:
| s=loc(src) { `Assgn(s) }
| s=loc(src) IF e = EXCL? cf = loc(preg)
  { `Cmov(s,(Src({d_pr = fst cf; d_aidxs = []}),snd cf),CfSet(e=None)) }
| s1=loc(src) op=binop s2=loc(src) { `Bop(op,s1,s2) }

base_instr :

| d=loc(dest) EQ rhs = assgn_rhs
    { match rhs with
      | `Bop(op,s1,s2) ->
        let d = dest_e_of_dest d in
        let s1 = src_e_of_src s1 in
        let s2 = src_e_of_src s2 in
        begin match op with
        | `Mul        -> Op(ThreeOp(O_IMul),d,(s1,s2))
        | `Plus       -> Op(Carry(O_Add,None,None),d,(s1,s2))
        | `Minus      -> Op(Carry(O_Sub,None,None),d,(s1,s2))
        | `BAnd       -> Op(ThreeOp(O_And),d,(s1,s2))
        | `Xor        -> Op(ThreeOp(O_Xor),d,(s1,s2))
        | `Shift(dir) -> Op(Shift(dir,None),d,(s1,s2))
        end
      | `Assgn(s) -> Assgn(fst d,fst s)
      | `Cmov(s,f,cmf) ->
        let d = dest_e_of_dest d in 
        let f = src_e_of_src f in 
        let s = src_e_of_src s in
        Op(CMov(cmf,f),d,(dest_to_src d,s))
    }

| cf_out=loc(cfout) d=loc(dest) oeq=opeq s=loc(src) cf_in=cfin?
    { let d = dest_e_of_dest d in
      let s = src_e_of_src s in
      let cf_out = dest_e_of_dest cf_out in
      let cin =
        match cf_in with
        | None -> None
        | Some(op,r) when op = oeq ->
          Some (Src({d_pr = pr_e_of_pr r; d_aidxs = []}))
        | Some _ -> failwith "cannot combine `+=` with `-` or `-=` with `+`"
      in
      match oeq with
      | `Add -> Op(Carry(O_Add,Some cf_out,cin),d,(dest_to_src d,s))
      | `Sub -> Op(Carry(O_Sub,Some cf_out,cin),d,(dest_to_src d,s))
      | `Shift(_) when cin<>None -> failwith "Shift does not take carry flag"
      | `Shift(dir) -> Op(Shift(dir,Some cf_out),d,(dest_to_src d,s))
      | `And -> failwith "And does not return carry flag"
      | `Xor -> failwith "Xor does not return carry flag" }
 
| d=loc(dest) oeq=opeq s=loc(src) cf_in=cfin?
    { let d = dest_e_of_dest d in
      let s = src_e_of_src s in
      let cin =
        match cf_in with
        | None -> None
        | Some(op,r) when op = oeq ->
          Some(Src({d_pr = pr_e_of_pr r; d_aidxs = []}))
        | Some _ -> failwith "cannot combine `+=` with `-` or `-=` with `+`"
      in
      match oeq with
      | `Add -> Op(Carry(O_Add,None,cin),d,(dest_to_src d,s))
      | `Sub -> Op(Carry(O_Sub,None,cin),d,(dest_to_src d,s))
      | `Shift(_) when cin<>None -> failwith "Shift does not take carry flag"
      | `Shift(dir) -> Op(Shift(dir,None),d,(dest_to_src d,s))
      | `And -> failwith "And does not take carry flag"
      | `Xor -> failwith "Xor does not take carry flag" }
    
| d1 = loc(dest) EQ s1=loc(src) STAR s2=loc(src)
    { let d1 = dest_e_of_dest d1 in
      let s1 = src_e_of_src s1 in
      let s2 = src_e_of_src s2 in 
      Op(ThreeOp(O_IMul),d1,(s1,s2)) }

| d1 = loc(dest) COMMA d2 = loc(dest) EQ s1=loc(src) STAR s2=loc(src)
    { let d1 = dest_e_of_dest d1 in
      let d2 = dest_e_of_dest d2 in
      let s1 = src_e_of_src s1 in
      let s2 = src_e_of_src s2 in
      Op(UMul(d1),d2,(s1,s2)) }

celse_if :
| ELIF c=pcond is=block
  { (c,is) }

celse :
| ELSE is = block
  { is }

instr :
| ir = base_instr SEMICOLON
  { Ins(Binstr(ir)) }

| d = decl SEMICOLON
  { Decl(d) }

| IF c=pcond
    i1s = block
    ies  = celse_if*
    mi2s = celse?
  { let ielse =
      Std.List.fold
        ~init:(Option.value ~default:[] mi2s)
        ~f:(fun celse (c,bi) -> [If(c,bi,celse)])
        (List.rev ies)
    in
    Ins(If(c,i1s,ielse)) }

| FOR cv=ID IN ce1=pexpr DOTDOT ce2=pexpr
    is = block
    { Ins(For(cv,ce1,ce2,is)) }

| d = preg EQCALL fname = ID args = tuple(preg) SEMICOLON
  { Ins(Call(fname,[d], args)) }

block :
| LCBRACE stmt = instr* RCBRACE
  { Std.List.map ~f:(function Ins(i) -> i | Decl(_) -> assert false) stmt }

stmt :
| stmt = instr* { stmt }

return :
| RETURN ret = tuple(preg) SEMICOLON { ret }

typ_indexed :
| LESS dims = separated_list(COMMA,pexpr) GREATER
  { dims }

typ_array :
| LBRACK dims = separated_list(COMMA,pexpr) RBRACK
  { dims }

typ :
| T_U64 ies = typ_indexed? dims=typ_array? 
  { U64(Option.value ~default:[] ies,Option.value ~default:[] dims) }
| T_BOOL
  { Bool }

typed_var :
| v = ID COLON t = typ
  { (v,t) }

typed_vars :
| vs = separated_nonempty_list(COMMA,ID) COLON t = typ
  { Std.List.map ~f:(fun v -> (v,t)) vs }

params :
| LESS tvars = separated_list(COMMA,typed_var) GREATER
  { tvars }

decl :
| REG trs = typed_vars
  { trs }
| FLAG trs = typed_vars
  { trs }

ret_ty :
| COLON tys = separated_list(STAR,typ) { tys }

efun :
| ext = EXTERN? FN name = ID
    ps = params?
    LPAREN args = separated_list(COMMA,typed_vars) RPAREN rty = ret_ty ?
  LCBRACE
    s = stmt
    r = return?
  RCBRACE
  { let ds = Std.List.filter_map ~f:(function Decl(ds) -> Some ds | _ -> None) s in
    let is = Std.List.filter_map ~f:(function Ins(i) -> Some i | _ -> None) s in
    let rtys = Option.value ~default:[] rty in
    let rets = Option.value ~default:[] r in
    if Std.List.length rets <> Std.List.length rtys then (
      let c_start = $startpos.Lexing.pos_cnum + 1 in
      let c_end = $endpos.Lexing.pos_cnum + 1 in
      let err = "mismatch between return type and return statement" in
      raise (ParserUtil.UParserError(c_start,c_end,err))
    );
    let rets = Std.List.zip_exn rets rtys in
    {
      ef_name   = name;
      ef_extern = ext<>None;
      ef_params = Option.value ~default:[] ps;
      ef_args   = List.concat args;
      ef_decls  = List.concat ds;
      ef_body   = is;
      ef_ret    = rets }
   }

efuns :
| efs = efun+ EOF { efs }
