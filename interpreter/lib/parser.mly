%token EOF
%start <Ast.t> main
%{ open! Ast %}

%%

let main :=
  | EOF; { ([]: Ast.t) }

%%
