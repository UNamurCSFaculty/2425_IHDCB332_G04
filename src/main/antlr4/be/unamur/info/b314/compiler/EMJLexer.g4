lexer grammar EMJLexer;

PACKAGE : '\u{1F4E6}'; // package/import
MAIN : '\u{1F3E0}'; // Main function

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
DOUBLE_EQUAL : '==';
COMMA : ',';
WITH : 'with';
LESS : '<';
GREATER : '>';
LEQ : '<=';
GEQ : '>=';
NOTEQUAL : '!=';

// logical operator
AND : '\u{1F91D}';
OR : '\u{2753}';
NOT : '\u{26D4}';

// types
INT_TYPE : '\u{1F522}';
BOOL_TYPE : '\u{1F51F}';
CHAR_TYPE : '\u{1F523}';
STRING_TYPE : '\u{1F521}';
TUPLE_TYPE : '\u{1F465}';
VOID_TYPE : '\u{1F300}';

//
IF : '\u{1F914}';
ELSE : '\u{1F928}';
SKIPPING : '\u{1F447}'; //Else branch of If without anything inside it
WHILE : '\u{267E}''\u{FE0F}';
FOR : '\u{1F501}';
STOP_THIEF : '\u{270B}'; //stop the thief
SOUND_TOGGLE : '\u{1F4FB}'; //activate/desactivate Cutebot sound
LIGHT_TOGGLE : '\u{1F6A8}'; //activate/desactivate lights of Cutebot
// --- Return ---
RETURN : '\u{21A9}'('\u{FE0F}')? ;        // ↩️
RETURN_VOID : '\u{21A9}'('\u{FE0F}')?'\u{1F300}'; // ↩️🌀
// tuple indexing
TUPLE_FIRST : '\u{0030}''\u{FE0F}';  // 0️ digit-zero (index 0)
TUPLE_SECOND : '\u{0031}''\u{FE0F}'; // 1️ digit-one (index 1)

// type values
INT_VALUE : (MINUS)?(DIGIT)+;
TRUE : '\u{2705}';
FALSE : '\u{274C}';

// map
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

//direction
UP_ARROW : '\u{2B06}''\u{FE0F}';
DOWN_ARROW : '\u{2B07}''\u{FE0F}';
RIGHT_ARROW : '\u{27A1}''\u{FE0F}';
LEFT_ARROW : '\u{2B05}''\u{FE0F}';

// whitespaces
WHITESPACE: (' ' | '\t' | ('\r')? '\n' | '\r')+ -> skip; // Skip ignores WHITESPACE in grammar

// type declarations
STRING_VALUE : '"'(~["\r\n])*'"';
CHAR_VALUE : '\'' (DIGIT | LETTER | SPACE) '\'';

// Définition améliorée des emojis
EMOJI: [\p{Emoji}\p{Emoji_Presentation}\p{Emoji_Modifier}\p{Emoji_Component}\p{Emoji_Modifier_Base}\p{Extended_Pictographic}\p{InMiscellaneous_Symbols}\p{InMiscellaneous_Symbols_And_Pictographs}\p{InSupplemental_Symbols_And_Pictographs}\p{InEmoticons}\p{InTransport_And_Map_Symbols}\p{InDingbats}\p{InEnclosed_Alphanumerics}\p{InEnclosed_Alphanumeric_Supplement}\p{InEnclosed_CJK_Letters_And_Months}\p{InEnclosed_Ideographic_Supplement}\p{InVariation_Selectors}\p{InVariation_Selectors_Supplement}\u200D\p{Regional_Indicator}\u{E0000}..\u{E007F}];
//EMOJIS : EMOJI+; //Normalement doit pouvoir être enlevé : Ayhan
EMOJI_ID : LEFT_BRACKET (EMOJI EMOJI*) RIGHT_BRACKET;

//com skip
BEGIN_COM : '\uD83D\uDD0A' -> pushMode(multiLineCom), skip ; //
ONE_LINE_COM : '\uD83D\uDCE2' ~[\r\n]* -> skip ; //  followed by text to end of line

// Multi-line comment mode
mode multiLineCom;
END_COM : '\uD83D\uDD08' -> popMode, skip ; // 
COMMENT_CONTENT : . -> skip ; // Skip everything in comment mode

// This rule is used to catch if we reach the EOF while still in multi-line comment mode
EOF_IN_COMMENT : EOF {
    throw new IllegalStateException("Unterminated block comment detected!");
};