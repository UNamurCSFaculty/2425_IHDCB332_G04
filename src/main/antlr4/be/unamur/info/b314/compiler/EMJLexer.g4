lexer grammar EMJLexer;

PACKAGE : '\u{1F4E6}'; //same as import
MAIN : '\u{1F3E0}' -> mode(Program) ;//Main function of program
// fragments
fragment DIGIT : '0'..'9';
fragment LETTER : ('a'..'z' | 'A'..'Z');
fragment SPACE : ' ';

// characters
SEMICOLON : ';';
LEFT_BRACKET : '[';
RIGHT_BRACKET : ']';
LEFT_PARENTHESIS : '(';
RIGHT_PARENTHESIS : ')';
LEFT_BRACE : '{';
RIGHT_BRACE : '}';
PLUS : '+';
MINUS : '-';
MULTIPLY : '*';
DIVIDE: '/';
EQUAL : '=';
COMMA : ',';
WITH : 'with';
LESS : '<';
GREATER : '>';
LEQ : '<=';
GEQ : '>=';
NOTEQUAL : '!=';

AND : '\u{1F91D}';
OR : '\u{2753}';
NOT : '\u{26D4}';


// predefined emojis
INT_TYPE : '\u{1F522}';
BOOL_TYPE : '\u{1F51F}';
CHAR_TYPE : '\u{1F523}';
STRING_TYPE : '\u{1F521}';
TUPLE_TYPE : '\u{1F465}';
IF : '\u{1F914}';
ELSE : '\u{1F928}';
Skipping : '\u{1F447}'; //Else branch of If without anything inside it
WHILE : '\u{267E}''\u{FE0F}';
FOR : '\u{1F501}';
STOP_THIEF : '\u{270B}'; //stop the thief
SOUND_TOGGLE : '\u{1F4FB}'; //activate/desactivate Cutebot sound
LIGHT_TOGGLE : '\u{1F6A8}'; //activate/desactivate lights of Cutebot
VOID_TYPE : '\u{1F300}';
RETURN : '\u{21A9}''\u{FE0F}';

// tuple indexing
TUPLE_FIRST : '\u{0030}''\u{FE0F}';  // 0️⃣ digit-zero (index 0)
TUPLE_SECOND : '\u{0031}''\u{FE0F}'; // 1️⃣ digit-one (index 1)

// type values
INT_VALUE : (MINUS)?(DIGIT)+;
TRUE : '\u{2705}';
FALSE : '\u{274C}';

MAP : '\u{1F5FA}''\u{FE0F}';
COP : '\u{1F694}';
ROAD : '\u{1F6E3}''\u{FE0F}';


OBSTACLE :
    '\u{1F30B}'          // volcano
  | '\u{1F3D8}''\u{FE0F}'// houses
  | '\u{1F6A7}'          // construction
  | '\u{1F69C}'          // tractor
  | '\u{1F30A}'     ;     // water-wave

THIEF: '\u{1F9B9}';


UP_ARROW : '\u{2B06}''\u{FE0F}';
DOWN_ARROW : '\u{2B07}''\u{FE0F}';
RIGHT_ARROW : '\u{27A1}''\u{FE0F}';
LEFT_ARROW : '\u{2B05}''\u{FE0F}';



// whitespaces
WHITESPACE: (' ' | '\t' | ('\r')? '\n' | '\r')+ -> skip; // Skip ignores WHITESPACE in grammar

// type declarations
STRING_VALUE : '"'(~["\r\n])*'"';
//BOOL_VALUE : TRUE|FALSE //ca fonctionne pas le LEXER doit uniquement contenir des tokens, pas des groupes de token.
CHAR_VALUE : '\'' (DIGIT | LETTER | SPACE) '\'';

//com skip
BEGIN_COM : '\uD83D\uDD0A' -> pushMode(multiLineCom), skip ; // 🔊
ONE_LINE_COM : '\uD83D\uDCE2' ~[\r\n]* -> skip ; // 📢 followed by text to end of line

// emoji structure, allows sequencing of emoji's
mode Program;
EMOJI : [\p{Emoji}]+;
EMOJIS : EMOJI+;
EMOJI_ID : LEFT_BRACKET EMOJIS RIGHT_BRACKET;
// Multi-line comment mode
mode multiLineCom;
END_COM : '\uD83D\uDD08' -> popMode, skip ; // 🔈
COMMENT_CONTENT : . -> skip ; // Skip everything in comment mode


