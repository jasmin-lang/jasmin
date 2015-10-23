%{
open IL_Lang
open Core_kernel
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
%token SHREQ SHLEQ XOREQ

%token STAR
%token BAND
%token MINUS
%token PLUS
%token LAND
%token SEMICOLON
%token QUESTION
%token EXCL DOTDOT COMMA
(* %token PERCENT *)
%token SHR
%token SHL
%token XOR

%token FOR
%token IN
%token IF
%token ELSE
%token TRUE
%token FALSE
%token EXTERN
%token FN
%token RETURN

%token <string> ID 
%token <int64>  INT

%left LAND
%nonassoc EXCL
%left MINUS PLUS
%left STAR

%type <IL_Lang.efun list> efuns

%start efuns

%%

(* -------------------------------------------------------------------- *)
(* Index expressions and conditions *)

%inline tuple(X):
| LPAREN l = separated_list(COMMA,X) RPAREN { l }
| l = separated_list(COMMA,X) { l }

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
| LPAREN c = ccond RPAREN { c }
| c1=cexpr o=ccondop c2=cexpr
  { Ccond(o,c1,c2) }

%inline preg :
| s=ID                        { (s,[]) }
| s=ID LBRACK ce=cexpr RBRACK { (s,[ce]) }
  (* FIXME: support multi-dimensional arrays *)


%inline mem:
| STAR LPAREN r=preg mi=offset? RPAREN
    { (r,Std.Option.value ~default:(Cconst Int64.zero) mi) }

(* -------------------------------------------------------------------- *)
(* Operators and assignments *)

offset:
| PLUS e=cexpr { e }
| MINUS e=cexpr { Cbinop(Cminus,Cconst(Int64.zero),e) }


src :
| r=preg { Sreg(r) }
| i=INT { Simm(i) }
| m = mem { Smem(fst m, snd m) }

dest :
| r = preg { Dreg(r) }
| m = mem { Dmem(fst m, snd m) }

cfin:
| PLUS  cf_in=preg { (Add,cf_in) }
| MINUS cf_in=preg { (Sub,cf_in) }

binop:
| PLUS  { `Plus }
| MINUS { `Minus }
| BAND  { `BAnd }
| STAR  { `Mul }
| SHR   { `Shr }
| SHL   { `Shl }
| XOR   { `Xor } 

%inline opeq:
| PLUSEQ  { Add }
| MINUSEQ { Sub }
| BANDEQ  { BAnd }
| SHREQ   { Shift(Right) }
| SHLEQ   { Shift(Left) }
| XOREQ   { Xor } 

(* -------------------------------------------------------------------- *)
(* instructions *)

%inline cfout:
| r_cf_out=preg QUESTION { r_cf_out }

assgn_rhs:
| s=src { `Assgn(s) }
| s=src IF e = EXCL? cf = ID { `Cmov(s,Sreg(cf,[]),CfSet(e=None)) }
| s1=src op=binop s2=src { `Bop(op,s1,s2) }


base_instr :
| d=dest EQ rhs = assgn_rhs
    { match rhs with
      | `Bop(op,s1,s2) ->
        begin match op with
        | `Mul   -> App(IMul,[d],[s1;s2])
        | `Plus  -> App(Add,[d],[s1;s2])
        | `Minus -> App(Sub,[d],[s1;s2])
        | `BAnd  -> App(BAnd,[d],[s1;s2])
        | `Shr   -> App(Shift(Right),[d],[s1;s2])
        | `Shl   -> App(Shift(Left),[d],[s1;s2])
        | `Xor   -> App(Xor,[d],[s1;s2])
        end
      | `Assgn(s) -> App(Assgn,[d],[s])
      | `Cmov(s,f,cmf) -> App(Cmov(cmf),[d],[dest_to_src d;s;f])
    }

| cf_out=cfout d=dest oeq=opeq s=src cf_in=cfin?
    { let cin =
        match cf_in with
        | None -> []
        | Some(op,r) when op = oeq -> [Sreg(r)]
        | Some _ -> failwith "cannot combine `+=` with `-` or `-=` with `+`"
      in
      App(oeq,[ Dreg(cf_out); d],[dest_to_src d;s]@cin) }

| d=dest oeq=opeq s=src cf_in=cfin?
    { let cin =
        match cf_in with
        | None -> []
        | Some(op,r) when op = oeq -> [Sreg(r)]
        | Some _ -> failwith "cannot combine `+=` with `-` or `-=` with `+`"
      in
      App(oeq,[d],[dest_to_src d;s]@cin) }

| ds = tuple(dest) EQ s1=src STAR s2=src
    { App(UMul,ds,[s1;s2]) }

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
| stmt = instr* { stmt }

return :
| RETURN ret = tuple(preg) SEMICOLON { ret }

efun :
| EXTERN FN name = ID LPAREN args = separated_list(COMMA,preg) RPAREN
  LCBRACE
    s = stmt
    r = return?
  RCBRACE
  { { ef_name = name; ef_args = args; ef_body = s;
      ef_ret = Option.value ~default:[] r } }
    

efuns :
| efs = efun+ EOF { efs }
