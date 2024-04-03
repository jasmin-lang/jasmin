%{

  open Syntax
  open Annotations

  let setsign c s = 
    match c with
    | None -> Some (Location.mk_loc (Location.loc s) (CSS(None, Location.unloc s)))
    | _    -> c

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
%token <Syntax.sign>GE
%token GLOBAL
%token <Syntax.sign>GT
%token <Syntax.sign>GTGT
%token HAT
%token IF
%token INLINE
%token <Syntax.sign> LE
%token <Syntax.sign> LT
%token               LTLT
%token MINUS
%token MUTABLE
%token NAMESPACE
%token PARAM
%token PERCENT
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
%token <Syntax.swsize>SWSIZE
%token <Syntax.svsize> SVSIZE
%token SLASH
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
%token <Z.t> INT
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
  | i=INT       { i }
  | MINUS i=INT { Z.neg i } 

simple_attribute:
  | i=int          { Aint i    }
  | id=NID         { Aid id    }
  | s=STRING       { Astring s }
  | s=keyword      { Astring s }
  | ws=utype       { Aws ws    }

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
| T_U8   { Wsize.U8   }
| T_U16  { Wsize.U16  }
| T_U32  { Wsize.U32  }
| T_U64  { Wsize.U64  }
| T_U128 { Wsize.U128 }
| T_U256 { Wsize.U256 }

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

swsize:
| s=SWSIZE { s }

svsize:
| s=SVSIZE { s }

castop1:
| s=swsize { CSS (Some (fst s), snd s) }
| s=svsize { CVS s }

castop:
| c=loc(castop1)? { c }

cast: 
| T_INT    { `ToInt }
| s=swsize { `ToWord s }

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
| SLASH       c=castop { `Div  c}
| PERCENT     c=castop { `Mod  c}
| AMP         c=castop { `BAnd c}
| PIPE        c=castop { `BOr  c}
| HAT         c=castop { `BXOr c}
| LTLT        c=castop { `ShL  c} 
| s=loc(GTGT) c=castop { `ShR (setsign c s)}
| ROR         c=castop { `ROR  c}
| ROL         c=castop { `ROL  c}
| EQEQ        c=castop { `Eq   c}
| BANGEQ      c=castop { `Neq  c}
| s=loc(LT)   c=castop { `Lt  (setsign c s)}
| s=loc(LE)   c=castop { `Le  (setsign c s)}
| s=loc(GT)   c=castop { `Gt  (setsign c s)}
| s=loc(GE)   c=castop { `Ge  (setsign c s)}

prim:
| SHARP x=ident { x }

%inline mem_ofs:
| PLUS e=pexpr { `Add, e }
| MINUS e=pexpr { `Sub, e }

%inline unaligned:
| ALIGNED { `Aligned }
| UNALIGNED { `Unaligned }

%inline mem_access:
| ct=parens(utype)? LBRACKET al=unaligned? v=var e=mem_ofs? RBRACKET
  { al, ct, v, e }
  
arr_access_len: 
| COLON e=pexpr { e }

arr_access_i:
| al=unaligned? ws=utype? e=pexpr len=arr_access_len? {ws, e, len, al }

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
    { let ct, v, e, al = ma in PEFetch (ct, v, e, al) }

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
| SLASH c=castop EQ  { `Div  c }
| PERCENT c=castop EQ  { `Mod  c }
| s=loc(GTGT)  c=castop EQ  { `ShR  (setsign c s) }
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

| WHILE is1=pblock? LPAREN b=pexpr RPAREN 
    { PIWhile (is1, b, None) }

| WHILE is1=pblock? LPAREN b=pexpr RPAREN is2=pblock
    { PIWhile (is1, b, Some is2) }
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

%inline pvardecl(S):
| ty=stor_type vs=separated_nonempty_list(S, var) { (ty, vs) }

annot_pvardecl: 
| a=annotations vd=pvardecl(empty) { (a,vd) }

pfunbody :
| LBRACE
    is = pinstr*
    rt = option(RETURN vs=tuple(var) SEMICOLON { vs })
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
    args = parens_tuple(annot_pvardecl)
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
