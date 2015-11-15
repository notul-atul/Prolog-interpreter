{
}

let smallLetter = ['a'-'z']
let capitalLetter = ['A'-'Z']
let specialChar = ['_' ''']  
let whitespace = [' ' '\t']
let newline = ['\n' '\r']
let digit = ['0' - '9']

rule token = parse
| whitespace+ { token lexbuf }
| newline { NEWLINE }
| "not" { NOT }
| ',' { COMMA }
| '.' { FULLSTOP }
| '-' { MINUS }
| '(' { LEFTPARENTHESIS }
| ')' { RIGHTPARENTHESIS }
| '[' { LEFTBOX }
| ']' { RIGHTBOX }
| ';' { SEMICOLON }
| ":-" { COLONDASH }
| "is" { IS }
| '=' { EQUALS }
| digit+ as dgt { NUM (int_of_string dgt) }
| smallLetter+  ( smallLetter* | capitalLetter* | digit* | specialChar* )* as p { PREDICATE (p)  }
| capitalLetter+ ( smallLetter* | capitalLetter* | digit* | specialChar* )* as v { VARIABLE  (v) }
| eof { EOF }

{}