%token EOF
%token PC STK
%token <int> REG
%token <int> INT
%token LPAREN RPAREN
%token PLUS MINUS AFFECT COMMA
%token O E RO RX RW RWX RWL RWLX URW URWX URWL URWLX
%token LOCAL GLOBAL DIRECTED

%left PLUS MINUS EXPR
%left UMINUS

%start <Irreg.t> main
%{ open! Irreg %}

%%

main:
  | EOF; { ([]: Irreg.t) }
  | r = reg ; AFFECT ; w = word ; p = main ;{ (r,w) :: p }

reg:
  | PC; { PC }
  | STK; { STK }
  | i = REG; { Reg i }

word:
  | e = expr %prec EXPR { WI (e) }
  | LPAREN
; p = perm ; COMMA ;
; g = locality ; COMMA
; b = addr ; COMMA
; e = addr ; COMMA
; a = addr
; RPAREN  { WCap (p, g, b, e, a) }

addr:
  | e = expr %prec EXPR { Addr (e) }
(* TODO support hexa addresses *)
(* TODO special addresses: min_addr, max_addr, stk_addr ... *)


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

%%
