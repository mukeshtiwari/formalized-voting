{
open Parser

}

rule lexeme = parse
 |['\n' '\r']+ {NEWLINE}
 |[' ' '\t']+ {lexeme lexbuf}
 |['0' - '9']+ as num { INT (int_of_string num) }
 |'A' | 'B' | 'C' | 'D' as v {CAND v}
 |'('  { LPAREN }
 |')' { RPAREN } 
 |';' { SEMI }
 |',' { COMMA }
 |eof { EOF }

