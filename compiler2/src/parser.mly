%{
%}

/*
(* ** Tokens *) */

%token EOF

%token LBRACK RBRACK LCBRACE RCBRACE LPAREN RPAREN
%token EQ
%token EQEQ
%token INEQ
%token PLUSEQ MINUSEQ BANDEQ MULEQ
%token LEQ
%token LESS
%token GREATER
%token GEQ
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
%token ELIF
%token TRUE
%token FALSE
%token PUB
%token MUT
%token FN
%token RETURN

%token MEM

%token <string> NID
%token <Bigint.zint> INT

(*
%nonassoc EXCL
%left LAND
%left LOR
%left MINUS PLUS
%left STAR
 *)

%type <unit> modul

%start modul

%%

modul:
| EOF { () }

