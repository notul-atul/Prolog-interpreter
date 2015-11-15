{}

let smallLetter = ['a'-'z']
let capitalLetter = ['A'-'Z']
let specialChar = ['_' ''']  
let whitespace = [' ' '\t']
let newline = ['\n' '\r']
let digit = ['0' - '9']

rule tokens = parse
| whitespace+ { tokens lexbuf }
| newline { NEWLINE }
| ',' { COMMA }
| '-' { MINUS }
| '.' { FULLSTOP }
| ''' ( smallLetter* | capitalLetter* | digit* | ['_']* | whitespace* )+ ''' as s { STRING( s ) }
| ''' { APOSTROPHE }
| '(' { LEFTPARENTHESIS }
| ')' { RIGHTPARENTHESIS }
| '[' { LEFTBOX }
| ']' { RIGHTBOX }
| ';' { SEMICOLON }
| digit+ as dgt { NUM (int_of_string dgt) }
| smallLetter+  ( smallLetter* | capitalLetter* | digit* | specialChar* )* as p { PREDICATE (p)  }
| capitalLetter+ ( smallLetter* | capitalLetter* | digit* | specialChar* )* as v { VARIABLE  (v) }
| eof { EOF }

{
		let lexbuf = Lexing.from_channel stdin in
		interact tokens lexbuf ;;
}