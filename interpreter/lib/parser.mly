%token EOF
%token PC
%token <int> REG
%token <int> INT
%token LPAREN RPAREN
%token PLUS MINUS
%token JMP JNZ MOVE LOAD STORE ADD SUB LT LEA RESTRICT SUBSEG ISPTR GETP GETB GETE GETA FAIL HALT
%token O E RO RX RW RWX
%start <Ast.t> main
%{ open! Ast %}

%%

let main :=
  | EOF; { ([]: Ast.t) }

%%
