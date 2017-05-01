%token <int> INT
%token <Lib.cand> CAND
%token LPAREN
%token RPAREN
%token COMMA
%token SEMI
%token NEWLINE
%token EOF


%start <(Lib.cand * int) list list> prog

%%

prog: ds = stmts EOF {ds};

stmts:
 |ds = separated_list(NEWLINE, stmtline) {ds} ;

stmtline:
 |vs = separated_list(SEMI,stmtone) {vs}

stmtone:
 |LPAREN; s = CAND; COMMA; n = INT; RPAREN {(s, n)} 
