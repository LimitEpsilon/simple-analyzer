%{       

open Syntax

let lbl = ref 0
let new_lbl () =
	let old_lbl = !lbl in
	incr lbl;
	old_lbl

let make_lblled cmd = LBL (0, cmd)

let rec relabel = function LBL (_, cmd) ->
	let lbl = new_lbl () in
	let cmd = match cmd with
	| SEQ (c1, c2) -> 
	  let c1 = relabel c1 in
	  let c2 = relabel c2 in
	  SEQ (c1, c2)
	| IF (e, c1, c2) -> 
	  let c1 = relabel c1 in
	  let c2 = relabel c2 in
	  IF (e, c1, c2)
	| WHILE (e, c) -> WHILE (e, relabel c)
	| no_subparts -> no_subparts
	in
	LBL (lbl, cmd)
%}

%token <int> NUM
%token TRUE FALSE READ
%token <string> ID
%token STAR AT
%token PLUS MINUS LT GT NOT ANDALSO ORELSE
%token COLONEQ SEMICOLON IF THEN ELSE
%token WHILE DO GOTO
%token LP RP
%token EOF

%right SEMICOLON
%nonassoc DO
%nonassoc ELSE
%nonassoc LT GT
%left PLUS MINUS
%left STAR
%right NOT
%left ANDALSO ORELSE

%start program
%type <Syntax.labelled_cmd> program

%%

program:
	  cmd EOF { relabel $1 }
	;

cmd: 
	  LP cmd RP { $2 }
	| ID COLONEQ expr { make_lblled (ASSIGN ($1, $3)) }
	| cmd SEMICOLON cmd { make_lblled (SEQ ($1, $3)) }
	| IF expr THEN cmd ELSE cmd { make_lblled (IF ($2, $4, $6)) }
	| WHILE expr DO cmd { make_lblled (WHILE ($2, $4)) }
	| GOTO expr { make_lblled (GOTO $2) }
	| STAR ID COLONEQ expr { make_lblled (PTRASSIGN ($2, $4)) }
	;
expr:
	| LP expr RP { $2 }
	| MINUS expr { MINUS ($2) }
	| NUM { NUM ($1) }
	| ID { VAR ($1) }
	| STAR ID { DEREF ($2) }
	| AT ID { AT ($2) }
	| expr PLUS expr { ADD ($1, $3) }
	| expr STAR expr { MULT ($1, $3) }
	| TRUE { TRUE }
	| FALSE { FALSE }
	| READ { READ }
	| NOT expr { NOT ($2)}
	| expr ANDALSO expr { ANDALSO ($1, $3) }
	| expr ORELSE expr { ORELSE ($1, $3) }
	| expr LT expr { LESS ($1, $3) }
	| expr GT expr { LESS ($3, $1) }
%%
