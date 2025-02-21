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

// predefined emojis
INT_TYPE : '\u{1F522}';

// type values
INT_VALUE : (MINUS)?(DIGIT)+;

// emoji structure
EMOJI : [\p{Emoji}]+;
EMOJIS : EMOJI+;
EMOJI_ID : LEFT_BRACKET EMOJIS RIGHT_BRACKET;

// whitespaces
WHITESPACE: (' ' | '\t' | ('\r')? '\n' | '\r')+ -> skip; // Skip ignores WHITESPACE in grammar