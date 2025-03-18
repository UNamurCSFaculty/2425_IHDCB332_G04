lexer grammar EMJLexer;

//    Basic lexical elements
fragment DIGIT : '0'..'9';
fragment LETTER : ('a'..'z' | 'A'..'Z');
fragment SPACE : ' ';
fragment EMOJI_UNICODE_RANGE : [\p{Emoji}\p{Emoji_Presentation}\p{Emoji_Modifier}\p{Emoji_Component}\p{Emoji_Modifier_Base}\p{Extended_Pictographic}\p{InMiscellaneous_Symbols}\p{InMiscellaneous_Symbols_And_Pictographs}\p{InSupplemental_Symbols_And_Pictographs}\p{InEmoticons}\p{InTransport_And_Map_Symbols}\p{InDingbats}\p{InEnclosed_Alphanumerics}\p{InEnclosed_Alphanumeric_Supplement}\p{InEnclosed_CJK_Letters_And_Months}\p{InEnclosed_Ideographic_Supplement}\p{InVariation_Selectors}\p{InVariation_Selectors_Supplement}\u200D\p{Regional_Indicator}\u{E0000}..\u{E007F}];

//    Basic syntax elements
SEMICOLON : ';';
LEFT_BRACKET : '[';
RIGHT_BRACKET : ']';
LEFT_PARENTHESIS : '(';
RIGHT_PARENTHESIS : ')';
LEFT_BRACE : '{';
RIGHT_BRACE : '}';
COMMA : ',';
WITH : 'with';

//    Arithmetic expressions
PLUS : '+';
MINUS : '-';
MULTIPLY : '*';
DIVIDE: '/';

//    Used in boolean expressions
EQUAL : '=';
DOUBLE_EQUAL : '==';
LESS : '<';
GREATER : '>';
LEQ : '<=';
GEQ : '>=';
NOTEQUAL : '!=';

//    Used to combine boolean expressions
AND : '\u{1F91D}';         // 🤝 (handshake)
OR : '\u{2753}';           // ❓ (question mark)
NOT : '\u{26D4}';          // ⛔ (no entry)

//    Emojis for data types
INT_TYPE : '\u{1F522}';    // 🔢 (numbers)
BOOL_TYPE : '\u{1F51F}';   // 🔟 (keycap 10)
CHAR_TYPE : '\u{1F523}';   // 🔣 (symbols)
STRING_TYPE : '\u{1F521}'; // 🔡 (lowercase)
TUPLE_TYPE : '\u{1F465}';  // 👥 (silhouettes)
VOID_TYPE : '\u{1F300}';   // 🌀 (cyclone)

//    Emojis for conditions and loops
IF : '\u{1F914}';          // 🤔 (thinking)
ELSE : '\u{1F928}';        // 🤨 (raised eyebrow)
SKIPPING : '\u{1F447}';    // 👇 (pointing down)
WHILE : '\u{267E}''\u{FE0F}'; // ♾️ (infinity)
FOR : '\u{1F501}';         // 🔁 (repeat)

//    Actions for Cutebot
STOP_THIEF : '\u{270B}';   // ✋ (raised hand)
SOUND_TOGGLE : '\u{1F4FB}'; // 📻 (radio)
LIGHT_TOGGLE : '\u{1F6A8}'; // 🚨 (light)

//    Function return handling
//------------------------------------------------------------------------------
RETURN : '\u{21A9}'('\u{FE0F}')? ;               // ↩️ (return)
RETURN_VOID : '\u{21A9}'('\u{FE0F}')?'\u{1F300}'; // ↩️🌀 (return void)


//    Emojis for indexing tuples (0 and 1)
//------------------------------------------------------------------------------
TUPLE_FIRST : '\u{0030}''\u{FE0F}';  // 0️ (digit-zero index 0)
TUPLE_SECOND : '\u{0031}''\u{FE0F}'; // 1️ (digit-one index 1)

//    Representation of constant values
INT_VALUE : (MINUS)?(DIGIT)+;
TRUE : '\u{2705}';         // ✅ (check)
FALSE : '\u{274C}';        // ❌ (cross)
STRING_VALUE : '"'(~["\r\n])*'"';
CHAR_VALUE : '\'' (DIGIT | LETTER | SPACE) '\'';

//    Emojis for game map
PACKAGE : '\u{1F4E6}';     // 📦 (package)
MAIN : '\u{1F3E0}';        // 🏠 (house)
MAP : '\u{1F5FA}''\u{FE0F}'; // 🗺️ (map)
COP : '\u{1F694}';         // 🚔 (police car)
ROAD : '\u{1F6E3}''\u{FE0F}'; // 🛣️ (road)
THIEF: '\u{1F9B9}';        // 🦹 (villain)

//    Map obstacles
OBSTACLE :
    '\u{1F30B}'           // 🌋 (volcano)
  | '\u{1F3D8}''\u{FE0F}' // 🏘️ (houses)
  | '\u{1F6A7}'           // 🚧 (construction)
  | '\u{1F69C}'           // 🚜 (tractor)
  | '\u{1F30A}'           // 🌊 (wave)
  ;

//    Direction emojis
UP_ARROW : '\u{2B06}''\u{FE0F}';     // ⬆️ (up)
DOWN_ARROW : '\u{2B07}''\u{FE0F}';   // ⬇️ (down)
RIGHT_ARROW : '\u{27A1}''\u{FE0F}';  // ➡️ (right)
LEFT_ARROW : '\u{2B05}''\u{FE0F}';   // ⬅️ (left)

//    Handling of whitespace and comments
WHITESPACE: (' ' | '\t' | ('\r')? '\n' | '\r')+ -> skip;

BEGIN_COM : '\uD83D\uDD0A' -> pushMode(multiLineCom), skip ; // 🔊 (speaker high)
ONE_LINE_COM : '\uD83D\uDCE2' ~[\r\n]* -> skip ; // 📢 (loudspeaker)

//    Emoji identifiers
EMOJI: EMOJI_UNICODE_RANGE;
EMOJI_ID : LEFT_BRACKET (EMOJI+) RIGHT_BRACKET;

//    Multi-line comments

mode multiLineCom;
END_COM : '\uD83D\uDD08' -> popMode, skip ; //
COMMENT_CONTENT : . -> skip ; // Skip all comment content