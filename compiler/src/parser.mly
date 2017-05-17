%{
  module L = Location
  module S = Syntax

  open Syntax
%}

%token EOF

%token LBRACKET
%token RBRACKET
%token LBRACE
%token RBRACE
%token LPAREN
%token RPAREN

%token T_BOOL
%token T_U8 T_U16 T_U32 T_U64 T_U128 T_U256 T_INT

%token SHARP
%token AMP
%token AMPAMP
%token AMPEQ
%token BANG
%token BANGEQ
%token COMMA
%token DOWNTO
%token ELSE
%token EQ
%token EQEQ
%token FALSE
%token FN
%token FOR
%token GE 
%token GEs
%token GT
%token GTs
%token GTGT
%token GTGTs
%token GTGTEQ
%token GTGTsEQ
%token HAT
%token HATEQ
%token IF
%token INLINE
%token LE
%token LEs
%token LT
%token LTs
%token LTLT
%token LTLTEQ
%token MINUS
%token MINUSEQ
%token PARAM
%token PIPE
%token PIPEEQ
%token PIPEPIPE
%token PLUS
%token PLUSEQ
%token RARROW
%token REG
%token RETURN
%token SEMICOLON
%token STACK
%token STAR
%token STAREQ
%token TO
%token TRUE
%token UNDERSCORE
%token WHILE
%token EXPORT

%token <string> NID
%token <Bigint.zint> INT

%left PIPEPIPE
%left AMPAMP
%left PIPE
%left HAT
%left AMP
%left EQEQ BANGEQ
%left LE LEs GE GEs LT LTs GT GTs
%left LTLT GTGT GTGTs
%left PLUS MINUS
%left STAR
%nonassoc BANG

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

ptype_r:
| T_BOOL
    { TBool }

| T_INT
    { TInt }

| ut=utype
    { TWord ut }

| ut=utype d=brackets(pexpr)
    { TArray (ut, d) }

ptype:
| x=loc(ptype_r) { x }

(* ** Index expressions
 * -------------------------------------------------------------------- *)

%inline peop1:
| BANG  { `Not }
| MINUS  { `Neg }

%inline peop2:
| PLUS     { `Add  }
| MINUS    { `Sub  }
| STAR     { `Mul  }
| AMPAMP   { `And  }
| PIPEPIPE { `Or   }
| AMP      { `BAnd }
| PIPE     { `BOr  }
| HAT      { `BXOr }
| LTLT     { `ShL  }
| GTGT     { `ShR  }
| GTGTs    { `Asr  }
| EQEQ     { `Eq   }
| BANGEQ   { `Neq  }
| LT       { `Lt   }
| LE       { `Le   }
| GT       { `Gt   }
| GE       { `Ge   }
| LTs      { `Lts  }
| LEs      { `Les  }
| GTs      { `Gts  }
| GEs      { `Ges  }

prim:
| SHARP x=ident { x }

pexpr_r:
| v=var
    { PEVar v }

| v=var i=brackets(pexpr)
    { PEGet (v, i) }

| TRUE
    { PEBool true }

| FALSE
    { PEBool false }

| i=INT
    { PEInt i }

| ct=parens(ptype)? LBRACKET v=var PLUS e=pexpr RBRACKET
    { PEFetch (ct, v, e) }

| o=peop1 e=pexpr
    { PEOp1 (o, e) }

| e1=pexpr o=peop2 e2=pexpr
    { PEOp2 (o, (e1, e2)) }

| e=parens(pexpr)
    { PEParens e }

| f=var args=parens_tuple(pexpr)
    { PECall (f, args) }

| f=prim args=parens_tuple(pexpr)
    { PEPrim (f, args) }

pexpr:
| e=loc(pexpr_r) { e }

(* -------------------------------------------------------------------- *)
peqop:
| EQ      { `Raw  }
| PLUSEQ  { `Add  }
| MINUSEQ { `Sub  }
| STAREQ  { `Mul  }
| GTGTEQ  { `ShR  }
| GTGTsEQ { `Asr  }
| LTLTEQ  { `ShL  }
| AMPEQ   { `BAnd }
| HATEQ   { `BXOr }
| PIPEEQ  { `BOr  }

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

| ct=parens(ptype)? LBRACKET v=var PLUS e=pexpr RBRACKET
    { PLMem (ct, v, e) }

plvalue:
| x=loc(plvalue_r) { x }

(* ** Control instructions
 * -------------------------------------------------------------------- *)

pinstr_r:
| x=tuple1(plvalue) o=peqop e=pexpr c=prefix(IF, pexpr)? SEMICOLON
    { PIAssign (x, o, e, c) }

| fc=loc(f=var args=parens_tuple(pexpr) { (f, args) })
    c=prefix(IF, pexpr)? SEMICOLON
    { let { L.pl_loc = loc; L.pl_desc = (f, args) } = fc in
      PIAssign ([], `Raw, L.mk_loc loc (PECall (f, args)), c) }

| IF c=pexpr i1s=pblock
    { PIIf (c, i1s, None) }

| IF c=pexpr i1s=pblock ELSE i2s=pblock
    { PIIf (c, i1s, Some i2s) }

| FOR v=var EQ ce1=pexpr TO ce2=pexpr is=pblock
    { PIFor (v, (`Up, ce1, ce2), is) }

| FOR v=var EQ ce1=pexpr DOWNTO ce2=pexpr is=pblock
    { PIFor (v, (`Down, ce1, ce2), is) }

| WHILE is1=pblock? LPAREN b=pexpr RPAREN is2=pblock?
    { PIWhile (is1, b, is2) }

pinstr:
| i=loc(pinstr_r) { i }

pblock_r:
| s=braces(pinstr*) { s }

pblock:
| s=loc(pblock_r) { s }

(* ** Function definitions
 * -------------------------------------------------------------------- *)

stor_type:
| sto=storage ty=ptype { (sto, ty) }

storage:
| REG    { `Reg    }
| STACK  { `Stack  }
| INLINE { `Inline }

pvardecl :
| ty=stor_type v=var { (ty, v) }

pfunbody :
| LBRACE
    vs = postfix(pvardecl, SEMICOLON)*
    is = pinstr*
    rt = option(RETURN vs=tuple(var) SEMICOLON { vs })
  RBRACE
    { { pdb_vars  = vs;
        pdb_instr = is;
        pdb_ret   = rt; } }

call_conv :
| EXPORT { `Export }
| INLINE { `Inline }

pfundef:
| cc=call_conv? FN
    name = ident
    args = parens_tuple(st=stor_type v=var { (st, v) })
    rty  = prefix(RARROW, tuple(stor_type))?
    body = pfunbody

  { { pdf_cc   = cc;
      pdf_name = name;
      pdf_args = args;
      pdf_rty  = rty ;
      pdf_body = body; } }

(* -------------------------------------------------------------------- *)
pparam:
| PARAM ty=ptype x=ident EQ pe=pexpr SEMICOLON
    { { ppa_ty = ty; ppa_name = x; ppa_init = pe; } }

(* -------------------------------------------------------------------- *)
top:
| x=pfundef { S.PFundef x }
| x=pparam  { S.PParam  x }

(* -------------------------------------------------------------------- *)
module_:
| pfs=loc(top)* EOF
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
| x=delimited(LBRACKET, X, RBRACKET) { x }

%inline braces(X):
| x=delimited(LBRACE, X, RBRACE) { x }

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
