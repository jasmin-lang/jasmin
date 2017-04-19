%{
  module L = Location
  module S = Syntax
%}

%token EOF

%token LBRACK RBRACK LCBRACE RCBRACE LPAREN RPAREN
%token EQ
%token EQEQ
%token INEQ
%token PLUSEQ MINUSEQ BANDEQ MULEQ
%token LT LE GT GE
%token SHREQ SHLEQ XOREQ OREQ
%token COLON
%token LARROW
%token DOLLAR

%token T_U8 T_U16 T_U32 T_U64 T_U128 T_U256 T_INT
%token T_BOOL

%token UNDERSCORE

%token STAR
%token BAND
%token MINUS
%token PLUS
%token LAND LOR
%token SEMICOLON
%token EXCL DOTDOT COMMA
%token SHR SHL XOR OR

%token REG STACK INLINE PARAM

%token FOR WHILE DO WHEN
%token IN
%token IF
%token ELSE
%token TRUE
%token FALSE
%token FN
%token RETURN

%token MEM

%token <string> NID
%token <Bigint.zint> INT

%nonassoc EXCL
%left LAND
%left LOR
%left MINUS PLUS
%left STAR

%type <unit> module_

%start module_

%%

(* ** Sources and destinations
 * -------------------------------------------------------------------- *)

%inline dest_get:
| pe=brackets(pexpr) { () }

%inline sdest_noloc :
| v=var idx=dest_get? { () }

%inline sdest :
| ld=loc(sdest_noloc) { () }

%inline rdest :
| sd=sdest { () }
| MEM LBRACK ptr=sdest PLUS pe=pexpr RBRACK { () }

%inline dest :
| l = loc(UNDERSCORE) { () }
| rd = rdest          { () }

param:
| lid=loc(NID) { () }

src :
| d=rdest                      { () }
| DOLLAR p=param               { () }
| DOLLAR LPAREN i=pexpr RPAREN { () }
| i=INT                        { () }

(* ** Index expressions and conditions
 * -------------------------------------------------------------------- *)

%inline pbinop :
| PLUS   { () }
| STAR  { () }
| MINUS { () }

%inline pcondop :
| EQEQ { () }
| INEQ { () }
| LT   { () }
| LE   { () }
| GT   { () }
| GE   { () }

var:
| lid=loc(NID) { () }

dexpr :
| p=param                    { () }
| i=INT                      { () }
| e1=dexpr o=pbinop e2=dexpr { () }
| LPAREN e1=dexpr RPAREN     { () }

pexpr :
| v=var                        { () }
| i=INT                        { () }
| e1=pexpr o=pbinop e2=pexpr   { () }
| LPAREN e1=pexpr RPAREN       { () }

%inline pbop :
| LAND { () }
| LOR  { () }

pcond :
| TRUE                        { () }
| FALSE                       { () }
| EXCL c=pcond                { () }
| c1=pcond o=pbop c2=pcond    { () }
| LPAREN c = pcond RPAREN     { () }
| c1=pexpr o=pcondop c2=pexpr { () }


%inline fcond :
| e=EXCL? v=var { () }

pcond_or_fcond :
| pc=pcond   { () }
| v=var      { () }
| EXCL v=var { () }

(* -------------------------------------------------------------------- *)
binop:
| PLUS { () }
| MINUS{ () }
| SHR  { () }
| SHL  { () }
| BAND { () }
| XOR  { () }
| STAR { () }
| OR   { () }

opeq:
| PLUSEQ  { () }
| MINUSEQ { () }
| SHREQ   { () }
| SHLEQ   { () }
| BANDEQ  { () }
| XOREQ   { () }
| OREQ    { () }
| MULEQ   { () }

(* ** Base instructions
 * -------------------------------------------------------------------- *)

%inline assgn_rhs_eq:
| s=src
    { () }

%inline assgn_rhs_mv:
| s=src
    { () }

| s=src IF e=EXCL? cf=rdest
    { () }

| s1=src op=binop s2=src
    { () }

| s1=src op1=binop s2=src op2=binop s3=src
    { () }

| fname=NID args=parens_tuple(src)
    { () }

%inline opeq_rhs:
| s  = src                  { () }
| s2 = src op2=binop s3=src { () }

%inline base_instr :
| ds=tuple1(dest) EQ rhs=assgn_rhs_mv SEMICOLON
    { () }

| WHEN _fc=fcond LCBRACE ds=tuple1(dest) EQ rhs=assgn_rhs_mv RCBRACE SEMICOLON
    { () }

| ds=tuple1(dest) COLON EQ rhs=assgn_rhs_eq SEMICOLON
    { () }

| ds=tuple1(dest) op=opeq rhs=opeq_rhs SEMICOLON
    { () }

(* ** Control instructions
 * -------------------------------------------------------------------- *)

%inline call :
| fname=NID args=parens_tuple(src)
    { () }
 
control_instr :
| lc=loc(call) SEMICOLON
    { () }

| IF c=pcond_or_fcond i1s=block
    { () }

| IF c=pcond_or_fcond i1s=block ELSE i2s=block
    { () }

| FOR cv=sdest IN LPAREN ce1=pexpr DOTDOT ce2=pexpr RPAREN is=block
    { () }

| WHILE fc=fcond is=block
    { () }

| DO is=block WHILE fc=fcond SEMICOLON
    { () }

(* ** Instructions, blocks, and statements
 * -------------------------------------------------------------------- *)

%inline instr :
| lbi = loc(base_instr)    { () }
| lci = loc(control_instr) { () }

block :
| LCBRACE stmt=instr* RCBRACE { () }

(* ** Function definitions
 * -------------------------------------------------------------------- *)

utype :
| T_U8   {   8 }
| T_U16  {  16 }
| T_U32  {  32 }
| T_U64  {  64 }
| T_U128 { 128 }
| T_U256 { 256 }

typ :
| ut=utype                   { () }
| T_INT                      { () }
| ut=utype d=brackets(dexpr) { () }
| T_BOOL                     { () }

stor_typ :
| sto=storage ty=typ { () }

%inline typed_vars_stor :
| st=stor_typ vs=loc(var) { () }

%inline storage:
| REG    { () }
| STACK  { () }
| INLINE { () }

ret_ty :
| LARROW tys=tuple(loc(stor_typ)) { tys }

%inline typed_vars_stor_var :
| st=stor_typ v=var { () }

arg_def :
| ltv=loc(typed_vars_stor_var)
    { () }

| lst=loc(stor_typ)
    { () }

code_sec:
| is = instr* { () }

var_sec:
| ds = terminated_list(SEMICOLON, typed_vars_stor) { () }

func_body :
| LCBRACE
    vs   = var_sec
    is   = code_sec
    lret = loc(option(RETURN ret=tuple(var) SEMICOLON { () }))
  RCBRACE
    { () }

func :
| FN lname=loc(NID)
    args = parens_tuple(arg_def)
    rty  = ret_ty?
    defs = func_body
    { () }

(* -------------------------------------------------------------------- *)
typed_params :
| t=typ vs=separated_nonempty_list(COMMA, NID) EQ pe=dexpr
    { () }

(* -------------------------------------------------------------------- *)
topparam:
| PARAM lps=loc(typed_params) SEMICOLON { () }

(* -------------------------------------------------------------------- *)
top:
| func     { () }
| topparam { () }

(* -------------------------------------------------------------------- *)
module_:
| pfs=top* EOF
    { () }

| error
   { S.parse_error (L.make $startpos $endpos) }

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X { L.mk_loc (L.make $startpos $endpos) x }

%inline parens(X):
| x=delimited(LPAREN, X, RPAREN) { x }

%inline brackets(X):
| x=delimited(LBRACK, X, RBRACK) { x }

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

terminated_list(S, X):
| x=X S xs=terminated_list(S, X) { x :: xs }
| { [] }
