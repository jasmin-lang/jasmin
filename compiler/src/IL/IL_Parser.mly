/*
(* * Parser for jasmin/rust *) */
/*
(* ** Header *) */
%{
open IL_Lang
(* open Core_kernel *)
open IL_ParseUtils
open IL_Utils

module L = ParserUtil.Lexing

%}

/*
(* ** Tokens *) */

%token EOF

%token LBRACK RBRACK LCBRACE RCBRACE LPAREN RPAREN
%token EQ
%token EQEQ
%token INEQ
%token LEQ
%token LESS
%token GREATER
%token GEQ
%token COLON
%token LARROW

%token T_U8 T_U16 T_U32 T_U64 T_U128 T_U256 T_INT
%token T_BOOL

%token UNDERSCORE

%token STAR
%token MINUS
%token PLUS
%token LAND LOR
%token SEMICOLON
%token EXCL DOTDOT COMMA

%token REG STACK INLINE CONST

%token FOR WHILE DO WHEN
%token IN
%token IF
%token ELSE
%token ELIF
%token TRUE
%token FALSE
%token PUB
%token MUT
%token VAREXCL
%token INLEXCL
%token CODEEXCL
%token DECL
%token FN
%token RETURN

%token MEM

%token <int> BCAST

%token <string * string> NID
%token <string> INT
%token <string> RUST_ATTRIBUTE
%token <string> RUST_SECTION
%token EXTERN_JASMIN

%nonassoc EXCL
%left LAND
%left LOR
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
| LBRACK pe = pexpr RBRACK { Ipexpr(pe) }

%inline sdest_noloc :
| v=var idx = dest_get?
    { { d_var = v; d_idx = idx; d_loc = L.dummy_loc } }
    (* we must fix up Ipexpr eventually to Ivar with context information *)

%inline sdest :
| ld=loc(sdest_noloc)
    { let (loc,d) = ld in { d with d_loc = loc } }

%inline rdest :
| sd=sdest                                      { Sdest(sd)     }
| MEM LBRACK ptr = sdest PLUS pe = pexpr RBRACK { Mem(ptr,pe)   }

%inline dest :
| l = loc(UNDERSCORE) { Ignore(fst l) }
| rd = rdest          { Rdest(rd)     }

param:
| lid=loc(NID) { mk_param lid }



src :
| d=rdest               { Src(d) }
| i=BCAST LPAREN pe = pexpr RPAREN
  { assert (i=64 || i=1);
    Imm(i,pe) } (* FIXME: fixed 64*)
(*| i=INT                 { Imm(64,Pconst(Arith.parse_big_int i)) }*)

(* ** Index expressions and conditions
 * -------------------------------------------------------------------- *)

%inline pbinop :
| PLUS    { Pplus  }
| STAR    { Pmult  }
| MINUS   { Pminus }

%inline pcondop :
| EQEQ    { Peq  }
| INEQ    { Pneq }
| LESS    { Plt  }
| LEQ     { Ple  }
| GREATER { Pgt  }
| GEQ     { Pge  }

var :
| lid = loc(NID) { mk_var lid }

dexpr :
| p=param                    { Patom(p)                            }
| i=INT                      { Pconst(Arith.parse_big_int i) }
| e1=dexpr o=pbinop e2=dexpr { Pbinop(o,e1,e2)                     }
| LPAREN e1=dexpr RPAREN     { e1                                  }

pexpr :
| v=var                        { Patom(Pvar(v))                }
| i=INT                        { Pconst(Arith.parse_big_int i) }
| e1=pexpr o=pbinop e2=pexpr   { Pbinop(o,e1,e2)               }
| LPAREN e1=pexpr RPAREN       { e1                            }

%inline pbop :
| LAND { Pand }
| LOR  { Por  }

pcond :
| TRUE                        { Pbool(true)      }
| FALSE                       { Pbool(false)     }
| EXCL c=pcond                { Pnot(c)          }
| c1=pcond o=pbop c2=pcond    { Pbop(o,c1,c2)    }
| LPAREN c = pcond RPAREN     { c                }
| c1=pexpr o=pcondop c2=pexpr { Pcmp(o,c1,c2)    }


%inline fcond :
| e=EXCL? v=var { {fc_neg=(e<>None); fc_var = v} }

pcond_or_fcond :
| pc = pcond   { Pcond(pc) }
| v  = var     { Fcond({fc_neg=false; fc_var = v}) }
| EXCL v = var { Fcond({fc_neg=true; fc_var = v}) }

(* ** Base instructions
 * -------------------------------------------------------------------- *)

%inline assgn_rhs_eq:
| s=src { `Assgn(s,Eq) }

%inline assgn_rhs_mv:
| s=src                      { `Assgn(s,Mv) }

| fname=NID args=paren_tuple(src)
    { `Call(mk_fname fname, args,NoInline) }

| INLEXCL LCBRACE fname=NID args=paren_tuple(src) RCBRACE
    { `Call(mk_fname fname, args,DoInline) }

%inline base_instr :
| ds=tuple_nonempty(dest) EQ rhs=assgn_rhs_mv SEMICOLON
    { mk_instr ds rhs (L.mk_loc ($startpos,$endpos)) }

| WHEN _fc=fcond LCBRACE ds=tuple_nonempty(dest) EQ rhs=assgn_rhs_mv RCBRACE SEMICOLON
    { mk_instr ds rhs (L.mk_loc ($startpos,$endpos)) }

| ds=tuple_nonempty(dest) COLON EQ rhs=assgn_rhs_eq SEMICOLON
    { mk_instr ds rhs (L.mk_loc ($startpos,$endpos)) }

(* ** Control instructions
 * -------------------------------------------------------------------- *)

%inline call :
| fname=NID args=paren_tuple(src) { (mk_fname fname, args) }
 
%inline control_instr :

| lc= loc(call) SEMICOLON
    { let (l,(fn,args)) = lc in
      Block([ { L.l_val=Call(fn,[],args,NoInline); L.l_loc=l} ],None) }

| INLEXCL LCBRACE lc= loc(call) RCBRACE SEMICOLON
    { let (l,(fn,args)) = lc in
      Block([ { L.l_val=Call(fn,[],args,DoInline); L.l_loc=l} ],None) }

| IF c=pcond_or_fcond i1s=block ies=celse_if* mi2s=celse?
    { mk_if c i1s mi2s ies }

| FOR cv=sdest IN LPAREN ce1=pexpr DOTDOT ce2=pexpr RPAREN is=block
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
| RETURN ret=tuple(var) { ret }

utype :
| T_U8   {   8 }
| T_U16  {  16 }
| T_U32  {  32 }
| T_U64  {  64 }
| T_U128 { 128 }
| T_U256 { 256 }

typ :
| ut = utype                               { Bty(U(ut)) }
| T_INT                                    { Bty(Int) }
| LBRACK ut=utype SEMICOLON d=dexpr RBRACK { Arr(U(ut),d) }
| T_BOOL                                   { Bty(Bool) }

stor_typ :
| sto=storage LPAREN ty=typ RPAREN { (sto,ty) }

%inline typed_vars_stor :
| vs=loc(var) COLON st=stor_typ
    { (fst vs, snd vs, st) }

%inline storage:
| REG    { Reg    }
| STACK  { Stack  }
| INLINE { Inline }

ret_ty :
| LARROW tys=tuple(loc(stor_typ)) { tys }

%inline typed_vars_stor_var :
| v=var COLON st=stor_typ
    { (v, st) }

arg_def :
| MUT? ltv = loc(typed_vars_stor_var)
    { let (l,(vs,st)) = ltv in (l,Some(vs),st) }
| MUT? lst = loc(stor_typ)
    { let (l,st) = lst in (l,None,st) }

func_decl :
| DECL LCBRACE pub=PUB? FN lname=loc(NID)
    args = paren_tuple(arg_def)
    rty  = ret_ty?
    SEMICOLON RCBRACE
    { (fst lname,
       Dproto { dp_fname=mk_fname @@ snd lname;
                dp_ret_ty=Util.get_opt [] rty;
                dp_is_pub=pub<>None;
                dp_arg_ty=args }) } 

%inline rust_sec:
| _rs=RUST_SECTION {  }

%inline code_sec:
| CODEEXCL LCBRACE is = instr*  RCBRACE { is }

%inline var_sec:
| VAREXCL LCBRACE ds = terminated_list(SEMICOLON,typed_vars_stor) RCBRACE
  { ds }

%inline func_body :
| LCBRACE
    vs  = var_sec?
    _rs = rust_sec?
    is  = code_sec?
    lret = loc(return?)
  RCBRACE
    { (Util.get_opt [] vs,Util.get_opt [] is,(fst lret, Util.get_opt [] (snd lret))) }

func :
| pub=PUB? FN lname=loc(NID)
    args = paren_tuple(arg_def)
    rty  = ret_ty?
    defs  = func_body
    { let (vars,instrs,ret) = defs in
      (fst lname,
       Dfun { df_fname=mk_fname @@ snd lname;
              df_ret_ty=Util.get_opt [] rty;
              df_is_pub=pub<>None;
              df_arg_list=args;
              df_instrs=instrs;
              df_vars=vars;
              df_ret=ret;
              })
    }

param_or_func :
| lf=func
    { [ lf ] }
| CONST lnid=loc(NID) COLON t=typ EQ pe=pexpr SEMICOLON
    { [ (fst lnid, Dparams([(snd lnid,t,pe)])) ] }
    (* FIXME: we should assert type=usize here *)
| ra=loc(RUST_ATTRIBUTE)
    { [(fst ra, Drust_attr(snd ra))] }
| rs=loc(RUST_SECTION)
    { [(fst rs, Drust_sec(snd rs))] }
| EXTERN_JASMIN
    { [] }
| fd=func_decl
    { [ fd ] }

modul :
| pfs=param_or_func+ EOF { mk_modul (List.concat pfs) }
