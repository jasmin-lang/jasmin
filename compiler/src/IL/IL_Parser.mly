%{
open IL_Lang
open Core_kernel
open Arith
open IL_ParseUtils

module P = ParserUtil
module L = ParserUtil.Lexing

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
%token SHREQ SHLEQ XOREQ OREQ
%token COLON
%token LARROW
%token DOLLAR

%token T_U64
%token T_BOOL

%token STAR
%token BAND
%token MINUS
%token PLUS
%token LAND
%token SEMICOLON
%token EXCL DOTDOT COMMA
%token SHR SHL XOR OR

%token REG FLAG PARAM STACK INLINE

%token FOR WHILE DO
%token IN
%token IF
%token ELSE
%token ELIF
%token TRUE
%token FALSE
%token EXTERN
%token FN
%token PYTHON
%token RETURN

%token MEM

%token <string> ID 
%token <string> INT

%left LAND
%nonassoc EXCL
%left MINUS PLUS
%left STAR

%type <IL_Lang.modul> modul

%start modul

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

dexpr :
| s=ID                       { Patom(s)                }
| i=INT                      { Pconst(U64.of_string i) }
| e1=dexpr o=pbinop e2=dexpr { Pbinop(o,e1,e2)         }
| LPAREN e1=dexpr RPAREN     { e1                      }

pexpr :
| s=ID                       { Patom(Pvar(s))          }
| DOLLAR s=ID                { Patom(Pparam(s))        }
| i=INT                      { Pconst(U64.of_string i) }
| e1=pexpr o=pbinop e2=pexpr { Pbinop(o,e1,e2)         }
| LPAREN e1=pexpr RPAREN     { e1                      }

pcond :
| TRUE                        { Ptrue          }
| FALSE                       { Pnot(Ptrue)    }
| EXCL c=pcond                { Pnot(c)        }
| c1=pcond LAND c2=pcond      { Pand(c1,c2)    }
| LPAREN c = pcond RPAREN     { c              }
| c1=pexpr o=pcondop c2=pexpr { Pcmp(o,c1,c2) }


%inline fcond :
| e= EXCL? d = dest { {fc_neg=(e<>None); fc_dest = d} }

pcond_or_fcond :
| pc = pcond  { Pcond(pc) }
| d  = dest   { Fcond({fc_neg=false; fc_dest = d}) }
| EXCL d = dest { Fcond({fc_neg=true; fc_dest = d}) }

(* -------------------------------------------------------------------- *)
(* * Sources and destinations *)

%inline dest_get:
| LBRACK idx = pexpr RBRACK { idx }

%inline dest_noloc :
| s=ID idx = dest_get?
    { { d_name = s; d_oidx = idx; d_loc = L.dummy_loc; d_odecl = None } }

%inline dest :
| ld=loc(dest_noloc)
    { let (d,loc) = ld in
      { d with d_loc = L.mk_loc loc } }

src :
| d=dest                       { Src(d)                       }
| DOLLAR i=ID                  { Imm(Patom(Pparam(i)))        }
| DOLLAR LPAREN i=pexpr RPAREN { Imm(i)                       }
| i=INT                        { Imm(Pconst(U64.of_string i)) }

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
| OR    { `Or }

opeq:
| PLUSEQ  { `Add }
| MINUSEQ { `Sub }
| SHREQ   { `Shift(Right) }
| SHLEQ   { `Shift(Left) }
| BANDEQ  { `And }
| XOREQ   { `Xor } 
| OREQ    { `Or } 
| MULEQ   { `Mul }

(* -------------------------------------------------------------------- *)
(* * Instructions *)

%inline assgn_rhs_eq:
| s=src { `Assgn(s,Eq) }

%inline assgn_rhs_mv:
| s=src { `Assgn(s,Mv) }

| s=src IF e=EXCL? cf=dest
    { `Cmov(e<>None,s,cf) }

| s1=src op=binop s2=src
    { `BinOp(op,s1,s2) }

| s1=src op1=binop s2=src op2=binop s3=src
    { `TernOp(op1,op2,s1,s2,s3) }

| fname=ID LPAREN args=separated_list(COMMA,src) RPAREN
    { `Call(fname, args) }

| MEM LBRACK ptr = src PLUS pe = pexpr RBRACK
    { `Load(ptr,pe) }

%inline opeq_rhs:
| s  = src                  { fun op d -> `BinOp(op,Src(d),s) }
| s2 = src op2=binop s3=src { fun op1 d -> `TernOp(op1,op2,Src(d),s2,s3) }

instr :
| ds=tuple_nonempty(dest) EQ rhs=assgn_rhs_mv SEMICOLON
    { mk_instr ds rhs (L.mk_loc ($startpos,$endpos)) }

| ds=tuple_nonempty(dest) COLON EQ rhs=assgn_rhs_eq SEMICOLON
    { mk_instr ds rhs (L.mk_loc ($startpos,$endpos)) }

| MEM LBRACK ptr = src PLUS pe = pexpr RBRACK EQ s = src SEMICOLON
    { Binstr(mk_store ptr pe s) }

| ds=tuple_nonempty(dest) op=opeq rhs=opeq_rhs SEMICOLON
    { let rhs = rhs op (Std.List.last_exn ds) in
      mk_instr ds rhs (L.mk_loc ($startpos,$endpos)) }

| fname=ID args=tuple(src) SEMICOLON
    { Binstr(Call(fname, [], args)) }

| IF c=pcond_or_fcond i1s=block ies=celse_if* mi2s=celse?
    { mk_if c i1s mi2s ies }

| FOR  cv=ID IN ce1=pexpr DOTDOT ce2=pexpr is=block
    { For(cv,ce1,ce2,is) }

| WHILE fc=fcond is=block
    { While(WhileDo,fc,is) }

| DO is=block WHILE fc=fcond SEMICOLON
    { While(DoWhile,fc,is) }

celse_if :
| ELIF c=pcond_or_fcond is=block { (c,is) }

celse :
| ELSE is=block { is }

linstr :
| li = loc(instr)
  { match li with
    | (instr,loc) -> L.{ l_val = instr; l_loc = mk_loc loc } }

block :
| LCBRACE stmt=linstr* RCBRACE { stmt }

stmt :
| stmt=linstr+ { stmt }

(* -------------------------------------------------------------------- *)
(* * Function definitions *)

return :
| RETURN ret=tuple(ID) SEMICOLON { ret }

typ_dim :
| LBRACK dim=dexpr RBRACK { (dim) }

typ :
| T_U64  odim=typ_dim? { match odim with None -> U64 | Some d -> Arr(d) }
| T_BOOL               { Bool      }

typed_vars :
| vs=separated_nonempty_list(COMMA,ID) COLON t=typ
    { Std.List.map ~f:(fun v -> (v,t)) vs }

%inline storage:
| REG    { Reg   }
| STACK  { Stack }
| FLAG   { Flag  }
| INLINE { Inline  }

decl :
| sto=storage trs=typed_vars  { Std.List.map ~f:(fun (n,t) -> (sto,n,t)) trs }

stor_typ :
| sto=storage ty=typ { (sto,ty) }

ret_ty :
| LARROW tys=separated_list(STAR,stor_typ) { tys }

decls :
| ds=terminated_list(SEMICOLON,decl) { ds }

%inline func_body :
| LCBRACE
    ds   = decls
    stmt = stmt?
    ret  = return?
  RCBRACE
  { Def(mk_fundef ds stmt ret) }
| SEMICOLON
  { Undef }
| EQ PYTHON s=ID SEMICOLON
  { Py(s) }

func :
| ext=EXTERN? FN name=ID
    args = paren_tuple(decl)
    rty  = ret_ty?
    def  = func_body
    { mk_func (L.mk_loc ($startpos,$endpos)) rty name ext args def }

param_or_func :
| f=func                       
  { Dfun(f) }
| PARAM ps=typed_vars SEMICOLON
  { Dparams(ps) }

modul :
| pfs=param_or_func+ EOF
  { mk_modul pfs }
