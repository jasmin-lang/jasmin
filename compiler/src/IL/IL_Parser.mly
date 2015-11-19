%{
open IL_Lang
open Core_kernel
open Arith
open IL_Utils

module P = ParserUtil
module L = Lexing

%}

/*======================================================================*/
/* * Tokens */

%token EOF

%token LBRACK RBRACK LCBRACE RCBRACE LPAREN RPAREN
%token EQ
%token INEQ
%token PLUSEQ MINUSEQ BANDEQ MULEQ
%token LEQ
%token LESS
%token GREATER
%token GEQ
%token SHREQ SHLEQ XOREQ
%token COLON
%token LARROW

%token T_U64
%token T_BOOL

%token STAR
%token BAND
%token MINUS
%token PLUS
%token LAND
%token SEMICOLON
%token EXCL DOTDOT COMMA
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
%token <string> INT

%left LAND
%nonassoc EXCL
%left MINUS PLUS
%left STAR

%type <IL_Lang.efun list> efuns

%start efuns

%%

(* -------------------------------------------------------------------- *)
(* * Utility productions *)

%inline loc(X):
| x=X { (x, ($startpos,$endpos) ) }

%inline tuple(X):
| LPAREN l=separated_list(COMMA,X) RPAREN { l }
| l=separated_list(COMMA,X)               { l }

%inline tuple_nonempty(X):
| LPAREN l=separated_nonempty_list(COMMA,X) RPAREN { l }
| l=separated_nonempty_list(COMMA,X)               { l }

%inline delim_tuple(S,X,E):
| l = delimited(S,separated_list(COMMA,X),E) { l }

%inline paren_tuple(X):
| l = delim_tuple(LPAREN,X,RPAREN) { l }

%inline angle_tuple(X):
| l = delim_tuple(LESS,X,GREATER) { l }

%inline bracket_tuple(X):
| l = delim_tuple(LBRACK,X,RBRACK) { l }

terminated_list(S,X):
| x=X S xs=terminated_list(S,X)
  { x::xs }
| { [] }

(* -------------------------------------------------------------------- *)
(* * Index expressions and conditions *)

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
| i=INT                      { Pconst(U64.of_string i) }
| e1=pexpr o=pbinop e2=pexpr { Pbinop(o,e1,e2) }
| LPAREN e1=pexpr RPAREN     { e1 }

pcond :
| TRUE                        { Ptrue }
| FALSE                       { Pnot(Ptrue) }
| EXCL c=pcond                { Pnot(c) }
| c1=pcond LAND c2=pcond      { Pand(c1,c2) }
| LPAREN c = pcond RPAREN     { c }
| c1=pexpr o=pcondop c2=pexpr { Pcond(o,c1,c2) }

(* -------------------------------------------------------------------- *)
(* * Sources and destinations *)

pr_index :
| ce=pexpr                 { Get(ce) }
| lb=pexpr DOTDOT ub=pexpr { All(lb,ub) }

%inline preg_noloc :
| s=ID idxs=angle_tuple(pr_index)?
    { { pr_name = s; pr_idxs = get_opt [] idxs; pr_loc = P.dummy_loc } }

%inline preg :
| lpr=loc(preg_noloc)
    { let (pr,loc) = lpr in
      let loc = P.loc_of_lexing_loc loc in
      { pr with pr_loc = loc} }

dest :
| r=preg arr=bracket_tuple(pr_index)?
    { { d_pr = r; d_aidxs = get_opt [] arr} }

src :
| d=dest { Src(d) }
| i=INT  { Imm(U64.of_string i) }

(* -------------------------------------------------------------------- *)
(* * Operators and assignments *)

binop:
| PLUS  { `Add }
| MINUS { `Sub }
| SHR   { `Shift(Right) }
| SHL   { `Shift(Left) }
| BAND  { `And }
| XOR   { `Xor }
| STAR  { `Mul }

opeq:
| PLUSEQ  { `Add }
| MINUSEQ { `Sub }
| SHREQ   { `Shift(Right) }
| SHLEQ   { `Shift(Left) }
| BANDEQ  { `And }
| XOREQ   { `Xor } 
| MULEQ   { `Mul }

(* -------------------------------------------------------------------- *)
(* * Instructions *)

%inline assgn_rhs:
| s=src
    { `Assgn(s) }

| s=src IF e=EXCL? cf=preg
    { `Cmov(s,Src({d_pr = cf; d_aidxs = []}),CfSet(e=None)) }

| s1=src op=binop s2=src
    { `BinOp(op,s1,s2) }

| s1=src op1=binop s2=src op2=binop s3=src
    { `TernaryOp(op1,op2,s1,s2,s3) }

| fname=ID args=tuple(src)
    { `Call(fname, args) }


%inline opeq_rhs:
| s = src
    { fun op d -> `BinOp(op,Src(d),s) }

| s2=src op2=binop s3=src
    { fun op1 d -> `TernaryOp(op1,op2,Src(d),s2,s3) }


instr :
| ds=tuple_nonempty(dest) EQ rhs=loc(assgn_rhs) SEMICOLON
    { mk_instr ds rhs }
 
| ds=tuple_nonempty(dest) op=opeq rhs_loc=loc(opeq_rhs) SEMICOLON
    { let (rhs_fun,loc) = rhs_loc in
      let rhs = rhs_fun op (Std.List.last_exn ds) in
      mk_instr ds (rhs,loc) }

| fname=ID args=tuple(src) SEMICOLON
    { Call(fname, [], args) }

| IF c=pcond i1s=block ies=celse_if* mi2s=celse?
    { mk_if c i1s mi2s ies }

| FOR cv=ID IN ce1=pexpr DOTDOT ce2=pexpr is=block
    { For(cv,ce1,ce2,is) }


celse_if :
| ELIF c=pcond is=block { (c,is) }

celse :
| ELSE is=block { is }

block :
| LCBRACE stmt=instr* RCBRACE { stmt }

stmt :
| stmt=instr* { stmt }

(* -------------------------------------------------------------------- *)
(* * Function definitions *)

return :
| RETURN ret=tuple(preg) SEMICOLON { ret }

typ_indexed :
| LESS dims=separated_list(COMMA,pexpr) GREATER { dims }

typ_array :
| LBRACK dims=separated_list(COMMA,pexpr) RBRACK { dims }

typ :
| T_U64 ies=typ_indexed? dims=typ_array? 
    { U64(get_opt [] ies, get_opt [] dims) }
| T_BOOL
    { Bool }

typed_vars :
| vs=separated_nonempty_list(COMMA,ID) COLON t=typ
    { Std.List.map ~f:(fun v -> (v,t)) vs }

%inline decl_type:
| REG  { () }
| FLAG { () }

decl :
| _d=decl_type trs=typed_vars  { trs }

ret_ty :
| LARROW tys=separated_list(STAR,typ) { tys }

decls :
| ds=terminated_list(SEMICOLON,decl)
    { ds }

efun :
| ext=EXTERN? FN name=ID
    ps   = angle_tuple(typed_vars)?
    args = paren_tuple(typed_vars)
    rty  = ret_ty?
  LCBRACE
    ds   = decls
    stmt = stmt
    ret  = return?
  RCBRACE
    { mk_efun $startpos $endpos rty ret name ext  ps args ds stmt }

efuns :
| efs=efun+ EOF { efs }
