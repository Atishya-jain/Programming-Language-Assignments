%{
open MyOcaml
open Printf
%}

%token <string> CONS
%token <string> VAR 
%token TRUE FALSE
%token OR AND XOR NEG NOT
%token LPAREN RPAREN
%token LSQ RSQ
%token EOF
%token END
%token CUT
%token FAIL
%token COND
%token APP
%token COMMA
%token EQU NOTEQ

%start main
%start goal
%type <MyOcaml.main> main
%type <MyOcaml.executable> goal
%%

main: 
	| EOF			 { [] }
	| clause main    { Prog($1)::($2) }
;

goal:
	| goal_list		{ AST($1) }
;

clause:
	| atom END		 { Clf(Fact(Head($1))) }
	| atom COND body_list	{ Clr(Rule(Head($1),($3))) }
;

body_list:
	| CUT END		 { [Body(CUT)] }
	| FAIL END		 { [Body(FAIL)] }
	| atom END       { [Body($1)] }
	| atom COMMA body_list  { Body($1) :: ($3) }
	| CUT COMMA body_list  { Body(CUT) :: ($3) }
	| FAIL COMMA body_list  { Body(FAIL) :: ($3) }
;

goal_list:
	| CUT END		 { [Goal(CUT)] }
	| FAIL END		 { [Goal(FAIL)] }
	| atom END       { [Goal($1)] }
	| atom COMMA goal_list  { Goal($1) :: ($3) }
	| CUT COMMA goal_list  { Goal(CUT) :: ($3) }
	| FAIL COMMA goal_list  { Goal(FAIL) :: ($3) }
;

atom:
	| NOT LPAREN atom RPAREN        { Node(("not"),[$3]) }
	| CONS LPAREN term_list RPAREN	{ Node(($1),($3)) }
	| LPAREN atom RPAREN			{ $2 }
	| term EQU term 				{ Node(("eq"),[$1;$3]) }
	| term NOTEQ term 				{ Node(("neq"),[$1;$3]) }
	| LSQ atom APP atom	RSQ			{ Node(("app"),[$2;$4]) }
;

term_list:
	| term 							{ [$1] }
	| term COMMA term_list 			{ ($1)::($3) }
;

term:
	| CONS 			 { Node($1,[]) }
	| VAR 			 { V(Var($1)) }
	| LPAREN term RPAREN { $2 }
	| atom			 { $1 }
;