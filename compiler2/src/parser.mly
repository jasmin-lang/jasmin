%{
  module L = Location
  module S = Syntax

  open Syntax
%}

%token EOF

%token LBRACK RBRACK LCBRACE RCBRACE LPAREN RPAREN
%token EQ
%token EQEQ
%token INEQ
%token PLUSEQ MINUSEQ BANDEQ MULEQ
%token LT LE GT GE
%token SHREQ SHLEQ XOREQ OREQ
%token LARROW
%token DOLLAR
%token UNDERSCORE

%token T_U8 T_U16 T_U32 T_U64 T_U128 T_U256 T_INT
%token T_BOOL

%token STAR
%token BAND
%token MINUS
%token PLUS
%token LAND LOR
%token SEMICOLON
%token BANG DOTDOT COMMA
%token SHR SHL XOR OR

%token REG STACK INLINE PARAM

%token FOR
%token WHILE
%token IN
%token IF
%token ELSE
%token TRUE
%token FALSE
%token FN
%token RETURN

%token <string> NID
%token <Bigint.zint> INT

%nonassoc BANG
%left LAND
%left LOR
%left MINUS PLUS
%left STAR

%type <Syntax.pprogram> module_

%start module_

%%

%inline ident:
| x=loc(NID) { x }

var:
| x=ident { x }

(* ** Type expressions
 * -------------------------------------------------------------------- *)

utype:
| T_U8   { `W8   }
| T_U16  { `W16  }
| T_U32  { `W32  }
| T_U64  { `W64  }
| T_U128 { `W128 }
| T_U256 { `W256 }

ptype_:
| T_BOOL
    { TBool }

| T_INT
    { TInt }

| ut=utype
    { TWord ut }

| ut=utype d=brackets(pexpr)
    { TArray (ut, d) }

(* ** Index expressions
 * -------------------------------------------------------------------- *)

%inline peop1:
| BANG  { `Not }

%inline peop2:
| PLUS  { `Add  }
| MINUS { `Sub  }
| STAR  { `Mul  }
| LAND  { `And  }
| LOR   { `Or   }
| BAND  { `BAnd }
| OR    { `BOr  }
| XOR   { `BXOr }
| SHL   { `Shl  }
| SHR   { `Shr  }
| EQEQ  { `Eq   }
| INEQ  { `Neq  }
| LT    { `Lt   }
| LE    { `Le   }
| GT    { `Gt   }
| GE    { `Ge   }

pexpr_r:
| v=var
    { PEVar v }

| v=var i=brackets(pexpr)
    { PEGet (v, i) }

| DOLLAR v=ident
    { PEParam v }

| TRUE
    { PEBool true }

| FALSE
    { PEBool false }

| i=INT
    { PEInt i }

| o=peop1 e=pexpr
    { PEOp1 (o, e) }

| e1=pexpr o=peop2 e2=pexpr
    { PEOp2 (o, (e1, e2)) }

| e=parens(pexpr)
    { PEParens e }

pexpr:
| e=loc(pexpr_r) { e }

(* -------------------------------------------------------------------- *)
peqop:
| EQ      { `Raw }
| PLUSEQ  { `Add }
| MINUSEQ { `Sub }
| SHREQ   { `ShR }
| SHLEQ   { `ShL }
| BANDEQ  { `And }
| XOREQ   { `XOr }
| OREQ    { `Or  }
| MULEQ   { `Mul }

(* ** Left value
 * -------------------------------------------------------------------- *)

(* FIXME: missing syntax for Lmem *)
plvalue_r:
| UNDERSCORE
    { PLIgnore }

| x=var
    { PLVar x }

| x=var i=brackets(pexpr)
    { PLArray (x, i) }

plvalue:
| x=loc(plvalue_r) { x }

(* ** Control instructions
 * -------------------------------------------------------------------- *)

pinstr_r:
| x=tuple1(plvalue) o=peqop e=pexpr SEMICOLON
    { PIAssign (x, o, e, None) }

| x=tuple1(plvalue) o=peqop e=pexpr IF c=pexpr SEMICOLON
    { PIAssign (x, o, e, Some c) }

| fname=ident args=parens_tuple(pexpr) SEMICOLON
    { PICall (fname, args) }

| IF c=pexpr i1s=pblock
    { PIIf (c, i1s, None) }

| IF c=pexpr i1s=pblock ELSE i2s=pblock
    { PIIf (c, i1s, Some i2s) }

| FOR v=var IN LPAREN ce1=pexpr DOTDOT ce2=pexpr RPAREN is=pblock
    { PIFor (v, (ce1, ce2), is) }

| WHILE b=pexpr is=pblock
    { PIWhile (b, is) }

pinstr:
| i=loc(pinstr_r) { i }

pblock_r:
| s=braces(pinstr*) { s }

pblock:
| s=loc(pblock_r) { s }

(* ** Function definitions
 * -------------------------------------------------------------------- *)

stor_type:
| sto=storage ty=ptype_ { (sto, ty) }

storage:
| REG    { `Reg    }
| STACK  { `Stack  }
| INLINE { `Inline }

pvardecl :
| ty=stor_type v=var { (ty, v) }

pfunbody :
| LCBRACE
    vs = postfix(pvardecl, SEMICOLON)*
    is = pinstr*
    rt = option(RETURN vs=tuple(var) SEMICOLON { vs })
  RCBRACE
    { { pdb_vars  = vs;
        pdb_instr = is;
        pdb_ret   = rt; } }

pfundef:
| FN
    name = ident
    args = parens_tuple(st=stor_type v=var? { (st, v) })
    rty  = prefix(LARROW, tuple(stor_type))?
    body = pfunbody

  { { pdf_name = name;
      pdf_args = args;
      pdf_rty  = rty ;
      pdf_body = body; } }

(* -------------------------------------------------------------------- *)
pparam:
| PARAM ty=ptype_ xs=plist1(ident, COMMA) EQ pe=pexpr SEMICOLON
    { { ppa_ty = ty; ppa_names = xs; ppa_init = pe; } }

(* -------------------------------------------------------------------- *)
top:
| x=pfundef { S.PFundef x }
| x=pparam  { S.PParam  x }

(* -------------------------------------------------------------------- *)
module_:
| pfs=top* EOF
    { pfs }

| error
   { S.parse_error (L.make $startpos $endpos) }

(* -------------------------------------------------------------------- *)
%inline plist1(X, S):
| s=separated_nonempty_list(S, X) { s }

%inline loc(X):
| x=X { L.mk_loc (L.make $startpos $endpos) x }

%inline prefix(S, X):
| S x=X { x } 

%inline postfix(X, S):
| x=X S { x }

%inline parens(X):
| x=delimited(LPAREN, X, RPAREN) { x }

%inline brackets(X):
| x=delimited(LBRACK, X, RBRACK) { x }

%inline braces(X):
| x=delimited(LCBRACE, X, RCBRACE) { x }

%inline angles(X):
| x=delimited(LT, X, GT) { x }

%inline rtuple(X):
| s=separated_list(COMMA, X) { s }

%inline rtuple1(X):
| s=separated_nonempty_list(COMMA, X) { s }

%inline tuple(X):
| s=parens(rtuple(X)) | s=rtuple(X) { s }

%inline tuple1(X):
| s=parens(rtuple1(X)) | s=rtuple1(X) { s }

%inline parens_tuple(X):
| s=parens(rtuple(X)) { s }

%inline angles_tuple(X):
| s=angles(rtuple(X)) { s }

%inline brackets_tuple(X):
| s=brackets(rtuple(X)) { s }
