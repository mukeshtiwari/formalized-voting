%token <int> INT
%token <char> CAND
%token LPAREN
%token RPAREN
%token COMMA
%token SEMI
%token NEWLINE
%token EOF


%start <(char * int) list list> prog

%%

prog: ds = stmts EOF {ds};

stmts:
 | {[]}
 | d = stmtline; NEWLINE; ds = stmts {d :: ds} ;

stmtline:
 | {[]}
 | v = stmtone; SEMI; vs = stmtline  {v :: vs}

stmtone:
 |LPAREN; s = CAND; COMMA; n = INT; RPAREN {(s, n)} 
