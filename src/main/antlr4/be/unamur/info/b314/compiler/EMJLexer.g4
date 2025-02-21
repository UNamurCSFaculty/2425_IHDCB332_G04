lexer grammar EMJLexer;

// fragments
fragment DIGIT : '0'..'9';
fragment LETTER : ('a'..'z' | 'A'..'Z');

// characters
SEMICOLON : ';';
LEFT_BRACKET : '[';
RIGHT_BRACKET : ']';
MINUS : '-';
EQUAL : '=';
COMMA : ',';
WITH : 'with';

// predefined emojis
INT_TYPE : '\u{1F522}';
BEGIN_COM : '\u{1F50A}';
END_COM : '\u{1F508}';
ONE_LINE_COM : '\u{1F4E2}';

// map emojis
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

// type values
INT_VALUE : (MINUS)?(DIGIT)+;

// emoji structure
EMOJI : [\p{Emoji}]+;
EMOJIS : EMOJI+;
EMOJI_ID : LEFT_BRACKET EMOJIS RIGHT_BRACKET;

// whitespaces
WHITESPACE: (' ' | '\t' | ('\r')? '\n' | '\r')+ -> skip; // Skip ignores WHITESPACE in grammar