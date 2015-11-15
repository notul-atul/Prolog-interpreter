%{
	open Printf;;

	type pred= Pred of string;;
	type var= Var of string;;

	type atom = ATOM of (pred* term list)
	and term = PREDTERM of pred
	|	VARTERM of var
	| NUMTERM of int
	| ATOMTERM of atom
	;;
	type eqcheck = EQCHECK of (term*term);;
	type subassgn = SUBASSGN of (term*term*term);;
	
	type bodycomp =
	| NTS
	| ATOMCOMP of atom
	| EQCHECKCOMP of eqcheck
	| SUBASSGNCOMP of subassgn
	;;
	
	let database= Hashtbl.create 1000;;
	
	let addClause cl = match cl with
	| [ATOMCOMP(ATOM(p, tl) )] -> if Hashtbl.mem database p then
		Hashtbl.replace database p ( ( Hashtbl.find database p )@[[ATOMCOMP(ATOM(p, tl) )]] ) 
		else Hashtbl.add database p [[ATOMCOMP(ATOM(p, tl) )]]
	|	ATOMCOMP(ATOM(p, tl) )::bd -> if Hashtbl.mem database p then
		Hashtbl.replace database p ( ( Hashtbl.find database p )@[ATOMCOMP(ATOM(p, tl) )::bd] )
		else Hashtbl.add database p [ATOMCOMP(ATOM(p, tl) )::bd]
	;;

	let noOfClause = ref 0 ;;

%}

%token NEWLINE
%token FULLSTOP
%token COMMA
%token LEFTPARENTHESIS RIGHTPARENTHESIS
%token LEFTBOX RIGHTBOX
%token COLONDASH
%token SEMICOLON
%token IS
%token MINUS EQUALS
%token NOT
%token <int> NUM
%token <string> PREDICATE
%token <string> VARIABLE
%token EOF

%start input
%type <unit> input

%%

input:	{  }
|	input line {  }
;

line: EOF { print_string ("Nunber of Clause Loaded = "^ (string_of_int ( !noOfClause ) )^"\n" ); flush stdout; noOfClause := 0 ; raise End_of_file }
|	NEWLINE	{ }
| fact NEWLINE { noOfClause := !noOfClause + 1 ; addClause $1 }
| rule NEWLINE { noOfClause := !noOfClause + 1 ; addClause $1 }
;

fact:	head FULLSTOP { [ATOMCOMP($1)] } ;

rule:	head COLONDASH body FULLSTOP { ATOMCOMP($1)::$3 } ;

body: head { [ATOMCOMP($1)] }
|	nothead { [NTS]@[ATOMCOMP($1)] }
|	equality { [EQCHECKCOMP($1)] }
|	notequality { [NTS]@[EQCHECKCOMP($1)] }
|	subtract { [SUBASSGNCOMP($1)] }
|	head COMMA body { [ATOMCOMP($1)]@$3 }
|	nothead COMMA body { $3@[NTS]@[ATOMCOMP($1)] }
|	equality COMMA body { [EQCHECKCOMP($1)]@$3 }
|	notequality COMMA body { $3@[NTS]@[EQCHECKCOMP($1)] }
|	subtract COMMA body { [SUBASSGNCOMP($1)]@$3 }
;

head:	predicate LEFTPARENTHESIS termlist RIGHTPARENTHESIS { ATOM($1, $3) } ;

nothead: NOT LEFTPARENTHESIS head RIGHTPARENTHESIS { $3 } ;

equality: LEFTPARENTHESIS variable EQUALS variable RIGHTPARENTHESIS { EQCHECK(VARTERM( $2 ), VARTERM( $4 )) }
| variable EQUALS variable { EQCHECK(VARTERM( $1 ), VARTERM( $3 )) }
;

notequality: NOT LEFTPARENTHESIS equality RIGHTPARENTHESIS { $3 } ;

subtract: variable IS variable MINUS variable { SUBASSGN(VARTERM( $1 ), VARTERM( $3 ), VARTERM($5)) } ;

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