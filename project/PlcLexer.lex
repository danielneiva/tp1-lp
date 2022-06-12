(* Plc Lexer *)

(* User declarations *)

open Tokens
type pos = int
type slvalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (slvalue, pos)token

fun keyword (string, lpos, rpos) =
    case string of
    "var"   => VAR(lpos, rpos)
    | "Bool"  => BOOL(lpos, rpos)
    | "else"  => ELSE(lpos, rpos)
    | "end"   => END(lpos, rpos)
    | "false" => FALSE(lpos, rpos)
    | "fn"    => FN(lpos, rpos)
    | "fun"   => FUN(lpos, rpos)
    | "hd"    => HD(lpos, rpos)
    | "if"    => IF(lpos, rpos)
    | "Int"   => INT(lpos, rpos)
    | "ise"   => ISE(lpos, rpos)
    | "match" => MATCH(lpos, rpos)
    | "Nil"   => NIL(lpos, rpos)
    | "print" => PRINT(lpos, rpos)
    | "rec"   => REC(lpos, rpos)
    | "then"  => THEN(lpos, rpos)
    | "tl"    => TL(lpos, rpos)
    | "true"  => TRUE(lpos, rpos)
    | "with"  => WITH(lpos, rpos)
    | "_"     => UNDER(lpos, rpos)
    |  _      => NAME(string, lpos, rpos)

(* A function to print a message error on the screen. *)
val error = fn x => TextIO.output(TextIO.stdOut, x ^ "\n")
val lineNumber = ref 0

(* Get the current line being read. *)
fun getLineAsString() =
    let
        val lineNum = !lineNumber
    in
        Int.toString lineNum
    end

(* Define what to do when the end of the file is reached. *)
fun eof () = Tokens.EOF(0,0)

fun strToInt s =
    case Int.fromString s of
        SOME x => x
        | NOME => raise Fail ("Wasn't able to convert the string '"^s^"'to integer.")

(* Initialize the lexer. *)
fun init() = ()
%%
%header (functor PlcLexerFun(structure Tokens: PlcParser_TOKENS));

alpha = [a-zA-Z];
digit = [0-9];
whitespace = [\ \t];
identifier = [a-zA-Z_][a-zA-Z_0-9]*;

%%

\n => (lineNumber := !lineNumber+1; lex());
{whitespace}+ => (lex());
{digit}+ => (NAT (strToInt(yytext), yypos, yypos));
{identifier} => (keyword(yytext, yypos, yypos));

"!"  => (NOT(yypos, yypos));
"&&" => (AND(yypos, yypos));
"+"  => (PLUS(yypos, yypos));
"-"  => (MINUS(yypos, yypos));
"*"  => (TIMES(yypos, yypos));
"/"  => (DIV(yypos, yypos));
"="  => (EQUAL(yypos, yypos));
"!=" => (NEQUAL(yypos, yypos));
"<"  => (LT(yypos, yypos));
"<=" => (LTE(yypos,yypos));
"::" => (CONS(yypos,yypos));
";"  => (SEMICOL(yypos, yypos));
"["  => (LBRACK(yypos, yypos));
"]"  => (RBRACK(yypos, yypos));
","  => (COMMA(yypos, yypos));
"{"  => (LBRACE(yypos, yypos));
"}"  => (RBRACE(yypos, yypos));
"("  => (LPAREN(yypos, yypos));
")"  => (RPAREN(yypos, yypos));
"|"  => (VBAR(yypos, yypos));
"=>" => (EQARROW(yypos, yypos));
"->" => (ARROW(yypos, yypos));
":"  => (COLON(yypos, yypos));

. =>(error("\n***Lexer error: bad character *** \n"); raise Fail ("Lexer error: bad character" ^ yytext));
