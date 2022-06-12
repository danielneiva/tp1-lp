%%

%name PlcParser

%pos int

%term VAR | FUN | REC | FN | END
  | IF | THEN | ELSE
  | MATCH | WITH
  | NOT | AND
  | UNDER | VBAR
  | HD | TL | ISE | CONS
  | PRINT
  | PLUS | MINUS | TIMES | DIV
  | EQUAL | NEQUAL | LT | LTE
  | COLON | SEMICOL | EQARROW | COMMA | ARROW | 
  | LBRACK | RBRACK
  | LBRACE | RBRACE
  | LPAREN | RPAREN
  | TRUE | FALSE
  | NIL | INT | BOOL 
  | NAME of string | NAT of int
  | EOF

%nonterm PROG of 
  | DECL of 
  | EXPR of 
  | ATOMICEXPR of 
  | APPEXPR of 
  | CONST of 
  | COMPS of 
  | MATCHEXPR of 
  | CONDEXPR of 
  | ARGS of 
  | PARAMS of 
  | TYPEDVAR of 
  | TYPE of 
  | ATOMICTYPE of 
  | TYPES of 

%right SEMIC ARROW CONS
%left ELSE AND EQUAL NEQUAL LT LTE PLUS MINUS TIMES DIV LBRACK
%nonassoc IF NOT HD TL ISE PRINT NAME

%eop EOF

%noshift EOF

%start Prog

%%
