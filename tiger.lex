type svalue = Tokens.svalue
type pos = int
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token
val comments = ref 0
val myString = ref ""
val stringPos = ref 0

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

fun eof () =
    let
        val pos = hd(!linePos)
    in
        if (!comments) <> 0 then ErrorMsg.error pos ("Error: There is an open comment.")
        else if String.compare(!myString,"") <> EQUAL then ErrorMsg.error pos ("Error: There is an open string.")
        else ();
        Tokens.EOF(pos,pos)
    end

%%
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));
%s STRING ESCAPE COMMENT;
%%
<INITIAL>type                  => (Tokens.TYPE(yypos, yypos+4));
<INITIAL>var                   => (Tokens.VAR(yypos, yypos+3));
<INITIAL>function              => (Tokens.FUNCTION(yypos, yypos+8));
<INITIAL>break                 => (Tokens.BREAK(yypos, yypos+5));
<INITIAL>of                    => (Tokens.OF(yypos, yypos+2));
<INITIAL>end                   => (Tokens.END(yypos, yypos+3));
<INITIAL>in                    => (Tokens.IN(yypos, yypos+2));
<INITIAL>nil                   => (Tokens.NIL(yypos, yypos+3));
<INITIAL>let                   => (Tokens.LET(yypos, yypos+3));
<INITIAL>do                    => (Tokens.DO(yypos, yypos+2));
<INITIAL>to                    => (Tokens.TO(yypos, yypos+2));
<INITIAL>for                   => (Tokens.FOR(yypos, yypos+3));
<INITIAL>while                 => (Tokens.WHILE(yypos, yypos+5));
<INITIAL>else                  => (Tokens.ELSE(yypos, yypos+4));
<INITIAL>then                  => (Tokens.THEN(yypos, yypos+4));
<INITIAL>if                    => (Tokens.IF(yypos, yypos+2));
<INITIAL>array                 => (Tokens.ARRAY(yypos, yypos+5));
<INITIAL>":="                  => (Tokens.ASSIGN(yypos, yypos+2));
<INITIAL>"|"                   => (Tokens.OR(yypos, yypos+1));
<INITIAL>"&"                   => (Tokens.AND(yypos, yypos+1));
<INITIAL>">="                  => (Tokens.GE(yypos, yypos+2));
<INITIAL>">"                   => (Tokens.GT(yypos, yypos+1));
<INITIAL>"<="                  => (Tokens.LE(yypos, yypos+2));
<INITIAL>"<"                   => (Tokens.LT(yypos, yypos+1));
<INITIAL>"<>"                  => (Tokens.NEQ(yypos, yypos+2));
<INITIAL>"="                   => (Tokens.EQ(yypos, yypos+1));
<INITIAL>"/"                   => (Tokens.DIVIDE(yypos, yypos+1));
<INITIAL>"*"                   => (Tokens.TIMES(yypos, yypos+1));
<INITIAL>"-"                   => (Tokens.MINUS(yypos, yypos+1));
<INITIAL>"+"                   => (Tokens.PLUS(yypos, yypos+1));
<INITIAL>"."                   => (Tokens.DOT(yypos, yypos+1));
<INITIAL>"}"                   => (Tokens.RBRACE(yypos, yypos+1));
<INITIAL>"{"                   => (Tokens.LBRACE(yypos, yypos+1));
<INITIAL>"]"                   => (Tokens.RBRACK(yypos, yypos+1));
<INITIAL>"["                   => (Tokens.LBRACK(yypos, yypos+1));
<INITIAL>")"                   => (Tokens.RPAREN(yypos, yypos+1));
<INITIAL>"("                   => (Tokens.LPAREN(yypos, yypos+1));
<INITIAL>";"                   => (Tokens.SEMICOLON(yypos, yypos+1));
<INITIAL>":"                   => (Tokens.COLON(yypos, yypos+1));
<INITIAL>","	                 => (Tokens.COMMA(yypos,yypos+1));
<INITIAL>[0-9]+                => (Tokens.INT(valOf (Int.fromString yytext), yypos, yypos+size yytext));
<INITIAL>[a-zA-Z][a-zA-Z0-9_]* => (Tokens.ID(yytext, yypos, yypos+size yytext));
<INITIAL>(\")                  => (stringPos := yypos; YYBEGIN STRING; continue());

<INITIAL>"/*"                  => (comments := (!comments+1); YYBEGIN COMMENT; continue());
<INITIAL>\n	                   => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>\t                    => (linePos := yypos+1 :: !linePos; continue());
<INITIAL>" "                   => (linePos := yypos+1 :: !linePos; continue());
<INITIAL>.                     => (ErrorMsg.error yypos ("Error - Illegal character sequence: " ^ yytext); continue());

<STRING>(\")                   => (let
                                      val toToken = !myString
								                   in
                                      myString := "";
                                      linePos := yypos+1 :: !linePos;
                                      YYBEGIN INITIAL;
                                      Tokens.STRING((toToken), !stringPos, hd(!linePos))
                                  end);
<STRING>"\\"                   => (YYBEGIN ESCAPE; continue());
<STRING>("\n"|"\t")        	   => (ErrorMsg.error yypos ("Error - Escape sequence used incorrectly in string"); continue());
<STRING>.                      => (myString := (!myString ^ yytext); YYBEGIN STRING; continue());

<ESCAPE>"\\"                   => (myString := (!myString) ^ "\\"; YYBEGIN STRING; continue());
<ESCAPE>"n"                    => (myString := (!myString) ^ "\n"; YYBEGIN STRING; continue());
<ESCAPE>"t"                    => (myString := (!myString) ^ "\t"; YYBEGIN STRING; continue());

<ESCAPE>[0-9]{3}               => (if ((valOf (Int.fromString yytext) > 31) andalso (valOf (Int.fromString yytext) < 256))
                                   then myString := (!myString) ^ String.str(Char.chr(valOf (Int.fromString yytext)))
                                   else ErrorMsg.error yypos ("Error - Illegal Ascii Character: " ^ yytext); YYBEGIN STRING; continue());

<ESCAPE>"^"[A-Z]			   => (myString := (!myString) ^ "\\" ^ yytext; YYBEGIN STRING; continue());
<ESCAPE>(" "|"\n"|"\t")+("\\") => (YYBEGIN STRING; continue());
<ESCAPE>(\")                   => (myString := (!myString) ^ "\""; YYBEGIN STRING; continue());
<ESCAPE>.                      => (ErrorMsg.error yypos ("Error - Illegal escape character: " ^ yytext); continue());

<COMMENT>"/*"                  => (comments := (!comments+1); YYBEGIN COMMENT; continue());
<COMMENT>\n	                   => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<COMMENT>\t                    => (linePos := yypos+1 :: !linePos; continue());
<COMMENT>"*/"                  => (comments := (!comments-1);
                                   if (!comments) = 0
                                   then (YYBEGIN INITIAL; continue())
                                   else continue());
<COMMENT>.                     => (continue());
