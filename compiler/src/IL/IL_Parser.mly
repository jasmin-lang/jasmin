%{

open IL_Lang
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


%inline cbinop :
| PLUS    { Cplus }
| STAR    { Cmult }
| MINUS   { Cminus }

%inline ccondop :
| EQ      { Ceq }
| INEQ    { Cineq }
| LESS    { Cless }
| LEQ     { Cleq }
| GREATER { Cgreater }
| GEQ     { Cgeq }

cexpr :
| s=ID  { Cvar(s) }
| i=INT { Cconst(i) }
| e1=cexpr o=cbinop e2=cexpr { Cbinop(o,e1,e2) }

ccond :
| TRUE         { Ctrue }
| FALSE        { Cnot(Ctrue) }
| EXCL c=ccond { Cnot(c) }
| c1=ccond LAND c2=ccond { Cand(c1,c2) }
| c1=cexpr o=ccondop c2=cexpr
  { Ccond(o,c1,c2) }

%inline vreg :
| s=ID                        { Vreg(s,[]) }
| s=ID LBRACK ce=cexpr RBRACK { Vreg(s,[ce]) }
  (* FIXME: support multi-dimensional arrays *)

%inline mreg :
| PERCENT r = ID { Mreg(r) }

reg :
| r = mreg { r }
| v = vreg { v }

%inline mem:
| STAR LPAREN r=reg mi=offset? RPAREN
    { (r,Std.Option.value ~default:(Cconst Int64.zero) mi) }

(* -------------------------------------------------------------------- *)
(* Operators and assignments *)

offset:
| PLUS e=cexpr { e }
| MINUS e=cexpr { Cbinop(Cminus,Cconst(Int64.zero),e) }


src :
| r=reg { Svar(r) }
| i=INT { Simm(i) }
| m = mem { Smem(fst m, snd m) }

dest :
| r = reg { Dvar(r) }
| m = mem { Dmem(fst m, snd m) }

cfin:
| PLUS  cf_in=ID { (Add,cf_in) }
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

| IF c=ccond
    i1s = block
    ELSE i2s = block
    { If(c,i1s,i2s) }

| FOR cv=ID IN ce1=cexpr DOTDOT ce2=cexpr
    is = block
    { For(cv,ce1,ce2,is) }

block :
| LCBRACE stmt = instr* RCBRACE { stmt }

stmt :
| stmt = instr* EOF { stmt }
