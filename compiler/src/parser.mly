%{

  open Syntax
  open Annotations

%}

%token EOF

%token LBRACKET
%token RBRACKET
%token LBRACE
%token RBRACE
%token LPAREN
%token RPAREN

%token T_BOOL
%token T_INT
%token <Syntax.swsize> T_W
%token <Syntax.sign> T_INT_CAST

%token SHARP
%token ALIGNED
%token AMP
%token AMPAMP
%token BANG
%token BANGEQ
%token COLON
%token COLONCOLON
%token COMMA
%token CONSTANT
%token DOT
%token DOWNTO
%token ELSE
%token EQ
%token EQEQ
%token EXEC
%token FALSE
%token FN
%token FOR
%token FROM
%token TYPE
%token <Syntax.sign option>GE
%token GLOBAL
%token <Syntax.sign option>GT
%token <Syntax.sign option>GTGT
%token HAT
%token IF
%token INLINE
%token <Syntax.sign option> LE
%token <Syntax.sign option> LT
%token               LTLT
%token MINUS
%token MUTABLE
%token NAMESPACE
%token PARAM
%token <Syntax.sign option> PERCENT
%token PIPE
%token PIPEPIPE
%token PLUS
%token POINTER
%token QUESTIONMARK
%token RARROW
%token REG
%token REQUIRE
%token RETURN
%token ROR
%token ROL
%token SEMICOLON
%token <Syntax.swsize> SWSIZE
%token <Syntax.svsize> SVSIZE
%token <Syntax.sign option> SLASH
%token STACK
%token STAR
%token TO
%token TRUE
%token UNALIGNED
%token UNDERSCORE
%token WHILE
%token EXPORT
%token ARRAYINIT
%token <string> NID
%token <Syntax.int_representation> INT
%token <string> STRING
%nonassoc COLON QUESTIONMARK
%left PIPEPIPE
%left AMPAMP
%left EQEQ BANGEQ
%left LE GE LT GT
%left PIPE
%left HAT
%left AMP
%left LTLT GTGT ROR ROL
%left PLUS MINUS
%left STAR SLASH PERCENT
%nonassoc BANG

%type <Syntax.pprogram> module_

%start module_

%%

%inline qident:
| x = separated_nonempty_list(COLONCOLON, NID) { String.concat "::" x }

%inline ident:
| x=loc(qident) { x }

var:
| x=ident { x }

(* ** Annotations
* -------------------------------------------------------------------- *)

keyword:
  | INLINE { "inline" }
  | EXPORT { "export" }
  | REG    { "reg" }
  | STACK  { "stack" }

annotationlabel:
  | id=ident {id}
  | id=loc(keyword) { id }
  | s=loc(STRING) { s }

int:
  | i=INT       { Syntax.parse_int i }
  | MINUS i=INT { Z.neg (Syntax.parse_int i ) }

simple_attribute:
  | i=int          { Aint i    }
  | id=NID         { Aid id    }
  | s=STRING       { Astring s }
  | s=keyword      { Astring s }
  | ws=utype       { Aws (fst ws) }

attribute:
  | EQ ap=loc(simple_attribute) { ap }
  | EQ s=loc(braces(struct_annot)) { Location.mk_loc (Location.loc s) (Astruct (Location.unloc s)) }

annotation:
  | k=annotationlabel v=attribute? { k, v }

struct_annot:
  | a=separated_list(COMMA, annotation) { a }

top_annotation:
  | SHARP a=annotation    { [a] }
  | SHARP LBRACKET a=struct_annot RBRACKET { a }

annotations:
  | l=list(top_annotation) { List.concat l }


(* ** Type expressions
 * -------------------------------------------------------------------- *)

utype:
| sw=T_W   { sw }

utype_array:
| ws=utype {TypeWsize ws}
| id=ident {TypeSizeAlias id}

ptype_r:
| T_BOOL
    { TBool }

| T_INT
    { TInt }

| ut=utype
    { TWord ut }

| ut=utype_array d=brackets(pexpr)
    { TArray (ut, d) }
| x=ident {TAlias x}

ptype:
| x=loc(ptype_r) { x }

swsize:
| s=SWSIZE { s }

svsize:
| s=SVSIZE { s }

castop1:
| s=swsize { CSS s }
| s=svsize { CVS s }

castop:
| c=loc(castop1)? { c }

cast:
| T_INT        { `ToInt (None) }
| s=T_INT_CAST { `ToInt (Some s)}
| s=swsize     { `ToWord s }

(* ** Index expressions
 * -------------------------------------------------------------------- *)
%inline peop1:
| BANG  c=castop    { `Not c  }
| MINUS c=castop    { `Neg c  }

%inline peop2:
| AMPAMP               { `And   }
| PIPEPIPE             { `Or    }
| PLUS        c=castop { `Add  c}
| MINUS       c=castop { `Sub  c}
| STAR        c=castop { `Mul  c}
| s=SLASH     c=castop { `Div (s,c)}
| s=PERCENT   c=castop { `Mod (s,c)}
| AMP         c=castop { `BAnd c}
| PIPE        c=castop { `BOr  c}
| HAT         c=castop { `BXOr c}
| LTLT        c=castop { `ShL  c}
| s=GTGT      c=castop { `ShR (s,c)}
| ROR         c=castop { `ROR  c}
| ROL         c=castop { `ROL  c}
| EQEQ        c=castop { `Eq   c}
| BANGEQ      c=castop { `Neq  c}
| s=LT        c=castop { `Lt (s,c)}
| s=LE        c=castop { `Le (s,c)}
| s=GT        c=castop { `Gt (s,c)}
| s=GE        c=castop { `Ge (s,c)}

prim:
| SHARP x=ident { x }

%inline mem_ofs:
| PLUS e=pexpr { `Add, e }
| MINUS e=pexpr { `Sub, e }

%inline unaligned:
| ALIGNED { `Aligned }
| UNALIGNED { `Unaligned }

%inline mem_access:
| ct=parens(loc(utype))? LBRACKET al=unaligned? v=var e=mem_ofs? RBRACKET
  { al, ct, v, e }

arr_access_len:
| COLON e=pexpr { e }

arr_access_i:
| al=unaligned? ws=loc(utype)? e=pexpr len=arr_access_len? {ws, e, len, al }

arr_access:
 | s=DOT?  i=brackets(arr_access_i) {
   let s = if s = None then Warray_.AAscale else Warray_.AAdirect in
   s, i }

pexpr_r:
| v=var
    { PEVar v }

| v=var i=arr_access
    { let aa, (ws, e, len, al) = i in PEGet (al, aa, ws, v, e, len) }

| TRUE
    { PEBool true }

| FALSE
    { PEBool false }

| i=INT
    { PEInt i }

| ma=mem_access
    { PEFetch ma }

| ct=parens(svsize) LBRACKET es=rtuple1(pexpr) RBRACKET
    { PEpack(ct,es) }

| ct=parens(cast) e=pexpr %prec BANG
    { PEOp1 (`Cast(ct), e) }

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

| e1=pexpr QUESTIONMARK e2=pexpr COLON e3=pexpr
    { PEIf(e1, e2, e3) }

pexpr:
| e=loc(pexpr_r) { e }

(* -------------------------------------------------------------------- *)
peqop:
|                EQ  { `Raw    }
| PLUS  c=castop EQ  { `Add  c }
| MINUS c=castop EQ  { `Sub  c }
| STAR  c=castop EQ  { `Mul  c }
| s=SLASH   c=castop EQ  { `Div  (s, c) }
| s=PERCENT c=castop EQ  { `Mod (s, c) }
| s=GTGT    c=castop EQ  { `ShR (s, c) }
| LTLT  c=castop EQ  { `ShL  c }
| ROR   c=castop EQ  { `ROR  c }
| ROL   c=castop EQ  { `ROL  c }
| AMP   c=castop EQ  { `BAnd c }
| HAT   c=castop EQ  { `BXOr c }
| PIPE  c=castop EQ  { `BOr  c }

(* ** Left value
 * -------------------------------------------------------------------- *)
plvalue_r:
| UNDERSCORE
    { PLIgnore }

| x=var
    { PLVar x }

| x=var i=arr_access
    { let a, (ws, e, len, al) = i in PLArray (al, a, ws, x, e, len) }

| ma=mem_access
    { let ct, v, e, al = ma in PLMem (ct, v, e, al) }

plvalue:
| x=loc(plvalue_r) { x }

(* ** Control instructions
 * -------------------------------------------------------------------- *)
implicites:
| QUESTIONMARK s=loc(braces(struct_annot)) { s }

plvalues:
| lv=tuple1(plvalue) { None, lv }
| LPAREN RPAREN { None, [] }
| s=implicites { Some s, [] }
| s=implicites COMMA lv=rtuple1(plvalue) { Some s, lv }

pinstr_r:
| ARRAYINIT x=parens(var) SEMICOLON
    { PIArrayInit x }

| x=plvalues o=peqop e=pexpr c=prefix(IF, pexpr)? SEMICOLON
    { PIAssign (x, o, e, c) }

| fc=loc(f=var args=parens_tuple(pexpr) { (f, args) })
    c=prefix(IF, pexpr)? SEMICOLON
    { let { Location.pl_loc = loc; Location.pl_desc = (f, args) } = fc in
      PIAssign ((None, []), `Raw, Location.mk_loc loc (PECall (f, args)), c) }

| s=pif { s }

| FOR v=var EQ ce1=pexpr TO ce2=pexpr is=pblock
    { PIFor (v, (`Up, ce1, ce2), is) }

| FOR v=var EQ ce1=pexpr DOWNTO ce2=pexpr is=pblock
    { PIFor (v, (`Down, ce2, ce1), is) }

| WHILE is1=pblock? LPAREN b=pexpr RPAREN is2=pblock?
    { PIWhile (is1, b, is2) }

| vd=postfix(pvardecl(COMMA?), SEMICOLON)
    { PIdecl vd }

pif:
| IF c=pexpr i1s=pblock
    { PIIf (c, i1s, None) }

| IF c=pexpr i1s=pblock ELSE i2s=pelse
    { PIIf (c, i1s, Some i2s) }

pelseif:
| s=loc(pif) { [([], s)] }

pelse:
| s=loc(pelseif) { s }
| s=pblock { s }

pinstr:
| a=annotations i=loc(pinstr_r)  { (a,i) }

pblock_r:
| s=braces(pinstr*) { s }

pblock:
| s=loc(pblock_r) { s }

(* ** Function definitions
 * -------------------------------------------------------------------- *)

stor_type:
| sto=storage ty=ptype { (sto, ty) }

annot_stor_type:
| a=annotations stoty=stor_type { (a,stoty) }

writable:
| CONSTANT    {`Constant }
| MUTABLE     {`Writable }

pointer:
| o=writable? POINTER { o }

ptr:
| o=pointer? {
   match o with
   | Some w -> `Pointer w
   | None   -> `Direct
   }

storage:
| REG    ptr=ptr { `Reg ptr }
| STACK  ptr=ptr { `Stack ptr }
| INLINE         { `Inline }
| GLOBAL         { `Global }


%inline decl:
| v=var { v, None }
| v=var EQ e=pexpr { v, Some e }

%inline pvardecl(S):
| ty=stor_type vs=separated_nonempty_list(S, loc(decl)) { (ty, vs) }

pparamdecl(S):
    ty=stor_type vs=separated_nonempty_list(S, var) { (ty, vs) }

annot_pparamdecl:
| a=annotations vd=pparamdecl(empty) { (a,vd) }

pfunbody :
| LBRACE
    is = pinstr*
    rt = loc(option(RETURN vs=tuple(var) SEMICOLON { vs }))
  RBRACE
    { { pdb_instr = is;
        pdb_ret   = rt; } }

call_conv :
| EXPORT { `Export }
| INLINE { `Inline }

pfundef:
|  pdf_annot = annotations
    cc=call_conv?
    FN
    name = ident
    args = parens_tuple(annot_pparamdecl)
    rty  = prefix(RARROW, tuple(annot_stor_type))?
    body = pfunbody

  { { pdf_annot;
      pdf_cc   = cc;
      pdf_name = name;
      pdf_args = args;
      pdf_rty  = rty ;
      pdf_body = body; } }

(* -------------------------------------------------------------------- *)
pparam:
| PARAM ty=ptype x=ident EQ pe=pexpr SEMICOLON
    { { ppa_ty = ty; ppa_name = x; ppa_init = pe; } }

(* -------------------------------------------------------------------- *)
pgexpr:
| e=pexpr { GEword e }
| LBRACE es = rtuple1(pexpr) RBRACE { GEarray es }
| e=loc(STRING) { GEstring e }

pglobal:
| pgd_type=ptype pgd_name=ident EQ pgd_val=pgexpr SEMICOLON
  { { pgd_type ; pgd_name ; pgd_val  } }

(* -------------------------------------------------------------------- *)
pexec:
| EXEC pex_name=ident pex_mem=parens_tuple(range) { { pex_name ; pex_mem } }

range:
| ptr=INT COLON size=INT { ptr, size }

(* -------------------------------------------------------------------- *)
prequire1:
| s=loc(STRING) { s }

from:
| FROM id=ident { id }

prequire:
| f=from? REQUIRE x=nonempty_list(prequire1) { f, x }

(* -------------------------------------------------------------------- *)
top:
| x=pfundef  { Syntax.PFundef x }
| x=pparam   { Syntax.PParam  x }
| x=pglobal  { Syntax.PGlobal x }
| x=pexec    { Syntax.Pexec   x }
| x=prequire { Syntax.Prequire x}
| TYPE name = ident EQ ty = ptype SEMICOLON
    { Syntax.PTypeAlias (name, ty)}
| NAMESPACE name = ident LBRACE pfs = loc(top)* RBRACE
    { Syntax.PNamespace (name, pfs) }
(* -------------------------------------------------------------------- *)
module_:
| pfs=loc(top)* EOF
    { pfs }

| error
   { Syntax.parse_error (Location.make $startpos $endpos) }

(* -------------------------------------------------------------------- *)
%inline empty:
| (* empty *) { () }

%inline plist1(X, S):
| s=separated_nonempty_list(S, X) { s }

%inline loc(X):
| x=X { Location.mk_loc (Location.make $startpos $endpos) x }

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

%inline brackets_tuple(X):
| s=brackets(rtuple(X)) { s }
