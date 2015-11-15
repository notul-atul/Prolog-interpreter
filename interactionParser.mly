%{
	let queryAksed = ref NTS ;;
%}

%token NEWLINE
%token FULLSTOP
%token COMMA
%token APOSTROPHE
%token MINUS
%token LEFTPARENTHESIS RIGHTPARENTHESIS
%token LEFTBOX RIGHTBOX
%token SEMICOLON
%token <string> STRING
%token <int> NUM
%token <string> PREDICATE
%token <string> VARIABLE
%token EOF

%start interact
%type <unit> interact

%%

interact: { }
|	interact ask { }
;

ask: LEFTBOX STRING RIGHTBOX FULLSTOP NEWLINE { print_string ( fileparser (String.sub $2 1 ( String.length $2 -2 ) ) ) ; flush stdout }
|	fact NEWLINE
{
	let unused = queryAksed := $1 in
	try
		print_string ( answerer true $1 ) ; flush stdout
	with Not_found -> print_string "false\n" ; flush stdout
}

|	SEMICOLON NEWLINE
{
	try
		print_string ( answerer false !queryAksed ) ; flush stdout
	with Not_found -> print_string "false\n"; flush stdout

}

| FULLSTOP NEWLINE { print_string ( destruct () ); flush stdout }
;

fact:	head FULLSTOP { ATOMCOMP($1) } ;

head:	predicate LEFTPARENTHESIS termlist RIGHTPARENTHESIS { ATOM($1, $3) } ;

termlist:	predicate { [PREDTERM($1)] }
|	variable { [VARTERM($1)] }
| NUM { [NUMTERM($1)] }
|	MINUS NUM { [NUMTERM(-$2)] }
| head { [ATOMTERM($1)] }
| termlist COMMA predicate { $1@[PREDTERM($3)] }
| termlist COMMA variable { $1@[VARTERM($3)] }
| termlist COMMA NUM { $1@[NUMTERM($3)] }
|	termlist COMMA MINUS NUM { $1@[NUMTERM(-$4)] }
| termlist COMMA head { $1@[ATOMTERM($3)] }
;

predicate: PREDICATE { Pred( $1 ) } ;

variable: VARIABLE { Var( $1 ) } ;