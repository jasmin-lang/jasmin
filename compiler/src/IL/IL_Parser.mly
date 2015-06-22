%{

open IL_Lang
open Util
open Core
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

%token STAR
%token BAND
%token MINUS
%token PLUS
%token LAND
%token SEMICOLON
%token QUESTION
%token EXCL DOTDOT COMMA
(* %token COMMA *)
%token PERCENT

%token FOR
%token IN
%token IF
%token ELSE
%token TRUE
%token FALSE

%token <string> ID 
%token <int64>  INT

%left LAND
%nonassoc EXCL
%left MINUS PLUS
%left STAR


%type <IL_Lang.stmt> stmt

%start stmt

%%

(* -------------------------------------------------------------------- *)
(* Index expressions and conditions *)


%inline ibinop :
| PLUS    { IPlus }
| STAR    { IMult }
| MINUS   { IMinus }

%inline icondop :
| EQ      { CEq }
| INEQ    { CInEq }
| LESS    { CLess }
| LEQ     { CLeq }
| GREATER { CGreater }
| GEQ     { CGeq }

iexpr :
| s=ID  { IVar(s) }
| i=INT { IConst(i) }
| i1=iexpr o=ibinop i2=iexpr { IBinOp(o,i1,i2) }

icond :
| TRUE         { ITrue }
| FALSE        { INot(ITrue) }
| EXCL i=icond { INot(i) }
| i1=icond LAND i2=icond { IAnd(i1,i2) }
| i1=iexpr o=icondop i2=iexpr
  { ICond(o,i1,i2) }

%inline var :
| s=ID                        { Nvar(s,[]) }
| s=ID LBRACK ie=iexpr RBRACK { Nvar(s,[ie]) }

%inline reg :
| PERCENT r = ID { Reg(r) }

indvar :
| r = reg { r }
| v= var { v }

%inline mem:
| STAR LPAREN iv=indvar mi=offset? RPAREN
    { (iv,Std.Option.value ~default:(IConst Int64.zero) mi) }

(* -------------------------------------------------------------------- *)
(* Operators and assignments *)

offset:
| PLUS i=iexpr { i }
| MINUS i=iexpr { IBinOp(IMinus,IConst(Int64.zero),i) }


src :
| iv=indvar { Svar(iv) }
| i=INT { Simm(i) }
| m = mem { Smem(fst m, snd m) }

dest :
| iv = indvar { Dvar(iv) }
| m = mem { Dmem(fst m, snd m) }

cfin:
| PLUS cf_in=ID { (Add,cf_in) }
| MINUS cf_in=ID { (Sub,cf_in) }

binop:
| PLUS  { `Plus }
| MINUS { `Minus }
| BAND  { `BAnd }
| STAR  { `Mult }

%inline opeq:
| PLUSEQ  { Add }
| MINUSEQ { Sub }
| BANDEQ  { BAnd }

(* -------------------------------------------------------------------- *)
(* instructions *)

%inline cfout:
| cf_out=ID QUESTION { cf_out }

assgn_rhs:
| s=src { `Right(s) }
| s1=src op=binop s2=src { `Left(op,s1,s2) }


base_instr :
| d=dest EQ rhs = assgn_rhs
    { match rhs with
      | `Left(op,s1,s2) ->
        begin match op with
        | `Mult  -> Mul(None,d,s1,s2)
        | `Plus  -> BinOpCf(Add,IgnoreCarry,d,s1,s2,IgnoreCarry)
        | `Minus -> BinOpCf(Sub,IgnoreCarry,d,s1,s2,IgnoreCarry)
        | `BAnd  -> BinOpCf(BAnd,IgnoreCarry,d,s1,s2,IgnoreCarry)
        end
      | `Right(s) -> Assgn(d,s)
    }

| cf_out=cfout d=dest oeq=opeq s=src cf_in=cfin?
    { let cin =
        match cf_in with
        | None -> IgnoreCarry
        | Some(op,s) when op = oeq -> UseCarry(s)
        | Some _ -> failwith "cannot combine `+=` with `-` or `-=` with `+`"
      in
      BinOpCf(oeq,UseCarry(cf_out),d,dest_to_src d,s,cin) }

| d=dest oeq=opeq s=src cf_in=cfin?
    { let cin =
        match cf_in with
        | None -> IgnoreCarry
        | Some(op,s) when op = oeq -> UseCarry(s)
        | Some _ -> failwith "cannot combine `+=` with `-` or `-=` with `+`"
      in
      BinOpCf(oeq,IgnoreCarry,d,dest_to_src d,s,cin) }

| LPAREN h=dest COMMA l=dest RPAREN EQ s1=src STAR s2=src
    { Mul(Some h,l,s1,s2) }

instr :
| ir = base_instr SEMICOLON { BInstr(ir) }

| IF c=icond
    i1s = block
    ELSE i2s = block
    { If(c,i1s,i2s) }

| FOR iv=ID IN ie1=iexpr DOTDOT ie2=iexpr
    is = block
    { For(iv,ie1,ie2,is) }

block :
| LCBRACE stmt = instr* RCBRACE { stmt }

stmt :
| stmt = instr* EOF { stmt }
