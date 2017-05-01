{
open Parser
}

rule lexeme = parse
 |[' ' '\t' '\r']+ {lexeme lexbuf}
 |['\n']+ {NEWLINE}
 |['0' - '9']+ as num { INT (int_of_string num) }
 |'A' | 'B' | 'C' | 'D' as v {CAND v}
 |'('  { LPAREN }
 |')' { RPAREN } 
 |';' { SEMI }
 |',' { COMMA }
 |eof { EOF }

