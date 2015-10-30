%{
open IL_Lang
open Core_kernel
open Arith

type instr_decl = Ins of instr_ut | Decl of (preg_ut * ty) list

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
%token COLON

%token T_U64
%token T_BOOL

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

%token REG

%token FOR
%token IN
%token IF
%token ELSE
%token ELIF
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

%type <IL_Lang.efun_ut list> efuns

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
| i=INT { Cconst(U64.of_int64 i) }
| e1=cexpr o=cbinop e2=cexpr { Cbinop(o,e1,e2) }
| LPAREN e1=cexpr RPAREN { e1 }

ccond :
| TRUE         { Ctrue }
| FALSE        { Cnot(Ctrue) }
| EXCL c=ccond { Cnot(c) }
| c1=ccond LAND c2=ccond { Cand(c1,c2) }
| LPAREN c = ccond RPAREN { c }
| c1=cexpr o=ccondop c2=cexpr
  { Ccond(o,c1,c2) }

%inline preg :
| s=ID                        
    { { pr_name = s; pr_index = []; pr_aux = () } }
| s=ID LESS ces=separated_list(COMMA,cexpr) GREATER
    { { pr_name = s; pr_index = ces; pr_aux = () } }

%inline mem:
| r=preg LBRACK i=cexpr RBRACK
    { (r,Cbinop(Cmult,i,Cconst (U64.of_int 8))) }

(* -------------------------------------------------------------------- *)
(* Operators and assignments *)

src :
| r=preg { Sreg(r) }
| i=INT { Simm(U64.of_int64 i) }
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
| s=src IF e = EXCL? cf = preg
  { `Cmov(s,Sreg(cf),CfSet(e=None)) }
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
      | `Cmov(s,f,cmf) -> App(CMov(cmf),[d],[dest_to_src d;s;f])
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

celse_if :
| ELIF c=ccond is=block
  { (c,is) }

celse :
| ELSE is = block
  { is }

instr :
| ir = base_instr SEMICOLON
  { Ins(BInstr(ir)) }

| d = decl SEMICOLON
  { Decl(d) }

| IF c=ccond
    i1s = block
    ies  = celse_if*
    mi2s = celse?
  { let ielse =
      Std.List.fold
        ~init:(Option.value ~default:[] mi2s)
        ~f:(fun celse (c,bi) -> [If(c,bi,celse)])
        (List.rev ies)
    in
    Ins(If(c,i1s,ielse)) }

| FOR cv=ID IN ce1=cexpr DOTDOT ce2=cexpr
    is = block
    { Ins(For(cv,ce1,ce2,is)) }

block :
| LCBRACE stmt = instr* RCBRACE
  { Std.List.map ~f:(function Ins(i) -> i | Decl(_) -> assert false) stmt }

stmt :
| stmt = instr* { stmt }

return :
| RETURN ret = tuple(preg) SEMICOLON { ret }

typ :
| T_U64
  { U64 }
| T_BOOL
  { Bool }
| T_U64 LBRACK ces = separated_list(COMMA,cexpr) RBRACK
  { Array(ces) }
| T_U64 LESS ces = separated_list(COMMA,cexpr) GREATER
  { Ivals(ces) }

typed_var :
| v = ID COLON t = typ
  { (v,t) }

typed_preg :
| vs = separated_nonempty_list(COMMA,preg) COLON t = typ
  { Std.List.map ~f:(fun v -> (v,t)) vs }

params :
| LESS tvars = separated_list(COMMA,typed_var) GREATER
  { tvars }

decl :
| REG trs = typed_preg
  { trs }

efun :
| ext = EXTERN? FN name = ID
    ps = params?
    LPAREN args = separated_list(COMMA,typed_preg) RPAREN
  LCBRACE
    s = stmt
    r = return?
  RCBRACE
  { let ds = Std.List.filter_map ~f:(function Decl(ds) -> Some ds | _ -> None) s in
    let is = Std.List.filter_map ~f:(function Ins(i) -> Some i | _ -> None) s in
    {
      ef_name   = name;
      ef_extern = ext<>None;
      ef_params = Option.value ~default:[] ps;
      ef_args   = Std.List.map ~f:(fun (pr,t) -> { pr with pr_aux = t }) (List.concat args);
      ef_decls  = Std.List.map ~f:(fun (pr,t) -> { pr with pr_aux = t }) (List.concat ds);
      ef_body   = is;
      ef_ret    = Option.value ~default:[] r } }
    

efuns :
| efs = efun+ EOF { efs }
