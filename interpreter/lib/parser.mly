%token EOF
%token PC STK
%token <int> REG
%token <int> INT
%token <string> LABELDEF
%token <string> LABEL
%token LPAREN RPAREN
%token PLUS MINUS
%token NOP JMP JNZ MOVE LOAD STORE ADD SUB LT LEA RESTRICT SUBSEG ISPTR
%token GETL GETP GETB GETE GETA FAIL HALT LOADU STOREU PROMOTEU
%token O E RO RX RW RWX RWL RWLX URW URWX URWL URWLX
%token LOCAL GLOBAL DIRECTED

%left PLUS MINUS EXPR
%left UMINUS

%start <Ir.t> main
%{ open! Ir %}

%%

main:
  | EOF; { ([]: Ir.t) }
  | NOP; p = main; { Nop :: p }
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
  | GETL; r1 = reg; r2 = reg; p = main; { GetL (r1, r2) :: p }
  | GETP; r1 = reg; r2 = reg; p = main; { GetP (r1, r2) :: p }
  | GETB; r1 = reg; r2 = reg; p = main; { GetB (r1, r2) :: p }
  | GETE; r1 = reg; r2 = reg; p = main; { GetE (r1, r2) :: p }
  | GETA; r1 = reg; r2 = reg; p = main; { GetA (r1, r2) :: p }
  | LOADU; r1 = reg; r2 = reg; c = reg_const; p = main; { LoadU (r1, r2, c) :: p }
  | STOREU; r = reg; c1 = reg_const; c2 = reg_const; p = main; { StoreU (r, c1, c2) :: p }
  | PROMOTEU; r = reg; p = main ; { PromoteU r :: p }
  | FAIL; p = main; { Fail :: p }
  | HALT; p = main; { Halt :: p }
  | lbl = LABELDEF; p = main; { Lbl lbl :: p }

reg:
  | PC; { PC }
  | STK; { STK }
  | i = REG; { Reg i }

reg_const:
  | r = reg; { Register r }
  | c = expr %prec EXPR { CP (Const (c)) }
  | p = perm ; g = locality ; { CP (Perm (p,g)) }

locality:
  | LOCAL; { Local }
  | GLOBAL; { Global }
  | DIRECTED; { Directed }

perm:
  | O; { O }
  | E; { E }
  | RO; { RO }
  | RX; { RX }
  | RW; { RW }
  | RWX; { RWX }
  | RWL; { RWL }
  | RWLX; { RWLX }
  | URW; { URW }
  | URWX; { URWX }
  | URWL; { URWL }
  | URWLX; { URWLX }

expr:
  | LPAREN; e = expr; RPAREN { e }
  | e1 = expr; PLUS; e2 = expr { AddOp (e1,e2) }
  | e1 = expr; MINUS; e2 = expr { SubOp (e1,e2) }
  | MINUS; e = expr %prec UMINUS { SubOp ((IntLit 0),e) }
  | i = INT { IntLit i }
  | lbl = LABEL { Label lbl }

%%
