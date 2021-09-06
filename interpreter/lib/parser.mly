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

main:
  | EOF; { ([]: Ast.t) }
  | JMP; r = reg; p = main; { (Jmp r :: p) }

reg:
  | PC; { PC }
  | i = REG; { R i }
%%
