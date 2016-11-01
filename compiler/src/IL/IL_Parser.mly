/*
(* * Parser for dmasm *) */
/*
(* ** Header *) */
%{
open IL_Lang
open Core_kernel
open Arith
open IL_ParseUtils
open IL_Utils

module P = ParserUtil
module L = ParserUtil.Lexing

%}

/*
(* ** Tokens *) */

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

%token REG PARAM STACK INLINE

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

%type <unit IL_Lang.modul> modul

%start modul

%%

(* ** Utility productions
 * -------------------------------------------------------------------- *)

%inline loc(X):
| x=X { (L.mk_loc ($startpos,$endpos), x) }

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

(* ** Sources and destinations
 * -------------------------------------------------------------------- *)

%inline dest_get:
| LBRACK idx = pexpr RBRACK { Iconst(idx) }

%inline dest_noloc :
| v=var idx = dest_get?
    { { d_var = v; d_idx = idx; d_loc = L.dummy_loc } }
    (* we must fix up Iconst eventually to Ivar with context information *)

%inline dest :
| ld=loc(dest_noloc)
    { let (loc,d) = ld in { d with d_loc = loc } }

param:
| lid=loc(ID) { mk_param lid }

src :
| d=dest                       { Src(d)                       }
| DOLLAR p=param               { Imm(Patom(Pparam(p)))        }
| DOLLAR LPAREN i=pexpr RPAREN { Imm(i)                       }
| i=INT                        { Imm(Pconst(U64.of_string i)) }

(* ** Index expressions and conditions
 * -------------------------------------------------------------------- *)

%inline pbinop :
| PLUS    { Pplus  }
| STAR    { Pmult  }
| MINUS   { Pminus }

%inline pcondop :
| EQ      { Peq      }
| INEQ    { Pineq    }
| LESS    { Pless    }
| LEQ     { Pleq     }
| GREATER { Pgreater }
| GEQ     { Pgeq     }

var :
| lid = loc(ID) { mk_var lid }

dexpr :
| p=param                    { Patom(p)                }
| i=INT                      { Pconst(U64.of_string i) }
| e1=dexpr o=pbinop e2=dexpr { Pbinop(o,e1,e2)         }
| LPAREN e1=dexpr RPAREN     { e1                      }

pexpr :
| v=var                      { Patom(Pvar(v))          }
| DOLLAR p=param             { Patom(Pparam(p))        }
| i=INT                      { Pconst(U64.of_string i) }
| e1=pexpr o=pbinop e2=pexpr { Pbinop(o,e1,e2)         }
| LPAREN e1=pexpr RPAREN     { e1                      }

pcond :
| TRUE                        { Ptrue         }
| FALSE                       { Pnot(Ptrue)   }
| EXCL c=pcond                { Pnot(c)       }
| c1=pcond LAND c2=pcond      { Pand(c1,c2)   }
| LPAREN c = pcond RPAREN     { c             }
| c1=pexpr o=pcondop c2=pexpr { Pcmp(o,c1,c2) }


%inline fcond :
| e=EXCL? v=var { {fc_neg=(e<>None); fc_var = v} }

pcond_or_fcond :
| pc = pcond   { Pcond(pc) }
| v  = var     { Fcond({fc_neg=false; fc_var = v}) }
| EXCL v = var { Fcond({fc_neg=true; fc_var = v}) }

(* ** Operators and assignments
 * -------------------------------------------------------------------- *)

binop:
| PLUS  { OpAdd }
| MINUS { OpSub }
| SHR   { OpShift(Right) }
| SHL   { OpShift(Left) }
| BAND  { OpAnd }
| XOR   { OpXor }
| STAR  { OpMul }
| OR    { OpOr }

opeq:
| PLUSEQ  { OpAdd }
| MINUSEQ { OpSub }
| SHREQ   { OpShift(Right) }
| SHLEQ   { OpShift(Left) }
| BANDEQ  { OpAnd }
| XOREQ   { OpXor } 
| OREQ    { OpOr } 
| MULEQ   { OpMul }

(* ** Base instructions
 * -------------------------------------------------------------------- *)

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
    { `Call(Fname.mk fname, args) }

| MEM LBRACK ptr = src PLUS pe = pexpr RBRACK
    { `Load(ptr,pe) }

%inline opeq_rhs:
| s  = src                  { fun op d -> `BinOp(op,Src(d),s) }
| s2 = src op2=binop s3=src { fun op1 d -> `TernOp(op1,op2,Src(d),s2,s3) }

%inline store :
| MEM LBRACK ptr = src PLUS pe = pexpr RBRACK EQ s = src
    { (ptr,pe,s) }


%inline base_instr :
| ds=tuple_nonempty(dest) EQ rhs=assgn_rhs_mv SEMICOLON
    { mk_instr ds rhs (L.mk_loc ($startpos,$endpos)) }

| ds=tuple_nonempty(dest) COLON EQ rhs=assgn_rhs_eq SEMICOLON
    { mk_instr ds rhs (L.mk_loc ($startpos,$endpos)) }

| lst = loc(store) SEMICOLON
    { let (l,(ptr,pe,s)) = lst in
      Block([ { L.l_val = mk_store ptr pe s; L.l_loc = l} ],None) }

| ds=tuple_nonempty(dest) op=opeq rhs=opeq_rhs SEMICOLON
    { let rhs = rhs op (Std.List.last_exn ds) in
      mk_instr ds rhs (L.mk_loc ($startpos,$endpos)) }

(* ** Control instructions
 * -------------------------------------------------------------------- *)

%inline call :
| fname=ID args=tuple(src) { (Fname.mk fname, args) }
 
%inline control_instr :

| lc=loc(call) SEMICOLON
    { let (l,(fn,args)) = lc in
      Block([ { L.l_val=Call(fn,[],args); L.l_loc=l} ],None) }

| IF c=pcond_or_fcond i1s=block ies=celse_if* mi2s=celse?
    { mk_if c i1s mi2s ies }

| FOR cv=dest IN ce1=pexpr DOTDOT ce2=pexpr is=block
    { For(cv,ce1,ce2,is,None) }

| WHILE fc=fcond is=block
    { While(WhileDo,fc,is,None) }

| DO is=block WHILE fc=fcond SEMICOLON
    { While(DoWhile,fc,is,None) }

celse_if :
| ELIF c=pcond_or_fcond is=block { (c,is) }

celse :
| ELSE is=block { is }

(* ** Instructions, blocks, and statements
 * -------------------------------------------------------------------- *)

%inline instr :
| lbi = loc(base_instr)    { let (loc,bi) = lbi in { L.l_val=bi; L.l_loc = loc} }
| lci = loc(control_instr) { let (loc,ci) = lci in { L.l_val=ci; L.l_loc = loc} }

block :
| LCBRACE stmt=instr* RCBRACE { stmt }

(* ** Function definitions
 * -------------------------------------------------------------------- *)

return :
| RETURN ret=tuple(var) SEMICOLON { ret }

typ_dim :
| LBRACK dim=dexpr RBRACK { (dim) }

typ :
| T_U64  odim=typ_dim? { match odim with None -> U64 | Some d -> Arr(d) }
| T_BOOL               { Bool }

stor_typ :
| sto=storage ty=typ { mk_sto_ty (sto,ty) (L.mk_loc ($startpos,$endpos)) }

%inline typed_vars_stor :
| vs=separated_nonempty_list(COMMA,dest) COLON st=stor_typ
    { (vs, st) } (* we parse dest here to prevent a conflict *)

%inline storage:
| REG    { Reg    }
| STACK  { Stack  }
| INLINE { Inline }

ret_ty :
| LARROW tys=separated_list(STAR,stor_typ) { tys }


%inline func_item:
| i = instr                     { FInstr(i) }
| d = typed_vars_stor SEMICOLON { FDecl(d)  }

%inline loc_func_item:
| lf = loc(func_item) { lf }

%inline func_body :
| LCBRACE
    fis  = loc_func_item*
    lret = loc(return?)
  RCBRACE
    { FunNative(fis,lret) }
| SEMICOLON
    { FunForeign(None) }
| EQ PYTHON s=ID SEMICOLON
    { FunForeign(Some(s)) }

%inline typed_vars_stor_var :
| vs=separated_nonempty_list(COMMA,var) COLON st=stor_typ
    { (vs, st) }

arg_def :
| ltv = loc(typed_vars_stor_var)
    { let (l,(vs,st)) = ltv in (l,Some(vs),st) }
| lst = loc(stor_typ)
    { let (l,st) = lst in (l,None,st) }

func :
| ext=EXTERN? FN lname=loc(ID)
    args = paren_tuple(arg_def)
    rty  = ret_ty?
    def  = func_body
    { (fst lname,
       mk_func (fst lname) (Fname.mk @@ snd lname) (Util.get_opt [] rty) ext args def) }

typed_params :
| vs=separated_nonempty_list(COMMA,ID) COLON t=typ
    { Std.List.map ~f:(fun v -> (v,t)) vs }

param_or_func :
| lf=func
    { (fst lf,Dfun(snd lf)) }
| PARAM lps=loc(typed_params) SEMICOLON
    { (fst lps, Dparams(snd lps)) }

modul :
| pfs=param_or_func+ EOF
  { mk_modul pfs }
