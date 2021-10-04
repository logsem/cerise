%token EOF
%token PC
%token <int> REG
%token <int> INT
%token LPAREN RPAREN
%token PLUS MINUS
%token JMP JNZ MOVE LOAD STORE ADD SUB LT LEA RESTRICT SUBSEG ISPTR GETP GETB GETE GETA FAIL HALT
%token O E RO RX RW RWX

%left PLUS MINUS
%left UMINUS
%start <Ast.t> main
%{ open! Ast %}

%%

main:
  | EOF; { ([]: Ast.t) }
  | JMP; r = reg; p = main; { Jmp r :: p }
  | JNZ; r1 = reg; r2 = reg; p = main; { Jnz (r1, r2) :: p }
  | MOVE; r = reg; c = reg_const; p = main; { Move (r, c) :: p }
  | LOAD; r1 = reg; r2 = reg; p = main; { Load (r1, r2) :: p }
  | STORE; r = reg; c = reg_const; p = main; { Store (r, c) :: p }
  | ADD; r = reg; c1 = reg_const; c2 = reg_const; p = main; { Add (r, c1, c2) :: p }
  | SUB; r = reg; c1 = reg_const; c2 = reg_const; p = main; { Sub (r, c1, c2) :: p }
  | LT; r = reg; c1 = reg_const; c2 = reg_const; p = main; { Lt (r, c1, c2) :: p }
  | LEA; r = reg; c = reg_const; p = main; { Lea (r, c) :: p }
  | RESTRICT; r = reg; c = reg_const; p = main; { Restrict (r, c) :: p }
  | SUBSEG; r = reg; c1 = reg_const; c2 = reg_const; p = main; { SubSeg (r, c1, c2) :: p }
  | ISPTR; r1 = reg; r2 = reg; p = main; { IsPtr (r1, r2) :: p }
  | GETP; r1 = reg; r2 = reg; p = main; { GetP (r1, r2) :: p }
  | GETB; r1 = reg; r2 = reg; p = main; { GetB (r1, r2) :: p }
  | GETE; r1 = reg; r2 = reg; p = main; { GetE (r1, r2) :: p }
  | GETA; r1 = reg; r2 = reg; p = main; { GetA (r1, r2) :: p }
  | FAIL; p = main; { Fail :: p }
  | HALT; p = main; { Halt :: p }

reg:
  | PC; { PC }
  | i = REG; { Reg i }

reg_const:
  | r = reg; { Register r }
  | c = expr %prec PLUS { Const (c) }
  | p = perm; { Perm p }

perm:
  | O; { O }
  | E; { E }
  | RO; { RO }
  | RX; { RX }
  | RW; { RW }
  | RWX; { RWX }

expr:
  | LPAREN; e = expr; RPAREN { e }
  | e1 = expr; PLUS; e2 = expr { e1 + e2 }
  | e1 = expr; MINUS; e2 = expr { e1 - e2 }
  | MINUS; e = expr %prec UMINUS { 0 - e }
  | i = INT { i }

%%
