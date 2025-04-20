parser grammar EMJParser;

//Parser uses tokens defined in EMJLexer.g4
options { tokenVocab = EMJLexer; }

//   Main entry point to distinguish between .map and .moj files
root
  : (mapFile | programFile) EOF
  ;

//Game map structure

mapFile
  : MAP WITH INT_VALUE COMMA INT_VALUE COMMA orientation SEMICOLON mapCell+
  ;

/**
 * Initial robot orientation on map
 * Can be up (north), down (south), left (west) or right (east)
 */
orientation
  : UP_ARROW     // ⬆️ (north)
  | RIGHT_ARROW  // ➡️ (east)
  | DOWN_ARROW   // ⬇️ (south)
  | LEFT_ARROW   // ⬅️ (west)
  ;

mapCell
  : COP      // 🚔 (police car)
  | ROAD     // 🛣️ (road)
  | OBSTACLE // 🌋🏘️🚧🚜🌊 (various obstacles)
  | THIEF    // 🦹 (thief)
  ;

//Global program file structure
programFile
  : importStatement?     // Optional map import
    mainFunction         // Required main function
    functionDecl*        // Optional user functions
    statement*           // Additional statements
  ;

importStatement
  : PACKAGE STRING_VALUE SEMICOLON?
  ;

//Data types
type
  : INT_TYPE    // 🔢 (integer)
  | BOOL_TYPE   // 🔟 (boolean)
  | CHAR_TYPE   // 🔣 (character)
  | STRING_TYPE // 🔡 (string)
  | tupleType   // Tuple of two elements
  ;

returnType
  : type        // Standard data type
  | VOID_TYPE   // 🌀 (void - no return)
  ;

tupleType
  : TUPLE_TYPE LEFT_PARENTHESIS type RIGHT_PARENTHESIS
  ;

//   Definition of functions (main and user)
mainFunction
  : VOID_TYPE MAIN LEFT_PARENTHESIS RIGHT_PARENTHESIS 
    LEFT_BRACE 
      statement+ 
      (VOID_TYPE SEMICOLON)? // Optional void return
    RIGHT_BRACE
  ;

functionDecl
  : returnType EMOJI_ID optionalParamList 
    LEFT_BRACE 
      statement* 
      returnStatement SEMICOLON // Required return
    RIGHT_BRACE
  ;

optionalParamList
  : LEFT_PARENTHESIS paramList? RIGHT_PARENTHESIS
  ;

paramList
  : param (COMMA param)*
  ;

param
  : type EMOJI_ID
  ;

//   Different instructions allowed in function body
statement
  : varDecl SEMICOLON         // Variable declaration
  | assignment SEMICOLON      // Assignment
  | functionCallStmt SEMICOLON // Function call
  | predefinedStmt SEMICOLON  // Predefined instruction
  | ifStatement               // Conditional statement
  | loopStatement             // Loop
  | returnStatement SEMICOLON // Function return
  ;

predefinedStmt
  : (STOP_THIEF | SOUND_TOGGLE | LIGHT_TOGGLE) LEFT_PARENTHESIS RIGHT_PARENTHESIS // ✋() Stop thief, // 📻() Toggle sound, // 🚨() Toggle lights
  | (UP_ARROW | DOWN_ARROW | RIGHT_ARROW | LEFT_ARROW) LEFT_PARENTHESIS INT_VALUE RIGHT_PARENTHESIS // ⬆️(n) Move up, // ⬇️(n) Move down, // ➡️(n) Move right, // ⬅️(n) Move left
  ;

varDecl
  : type EMOJI_ID (EQUAL expression)?
  ;

assignment
  : leftExpression EQUAL expression
  ;

leftExpression
  : EMOJI_ID (TUPLE_FIRST | TUPLE_SECOND)?
  ;

functionCallStmt
  : functionCall
  ;

functionCall
  : EMOJI_ID LEFT_PARENTHESIS argumentList? RIGHT_PARENTHESIS
  ;

argumentList
  : expression (COMMA expression)*
  ;

ifStatement
  : IF LEFT_PARENTHESIS expression RIGHT_PARENTHESIS block
    (ELSE block | ELSE LEFT_BRACE SKIPPING SEMICOLON RIGHT_BRACE)?
  ;

loopStatement
  : WHILE LEFT_PARENTHESIS expression RIGHT_PARENTHESIS block  // ♾️(condition) { ... }
  | FOR LEFT_PARENTHESIS expression RIGHT_PARENTHESIS block    // 🔁(condition) { ... }
  ;

returnStatement
  : RETURN expression?  // ↩️ expression - return with optional value
  | RETURN VOID_TYPE    // ↩️ 🌀 - explicit void return (method 1)
  | VOID_TYPE           // 🌀 - explicit void return (method 2)
  | RETURN_VOID         // ↩️🌀 - explicit void return (method 3)
  ;

//Hierarchy for calculations and conditions
expression
  : orExpression
  ;

orExpression
  : andExpression (OR andExpression)*  // expr ❓ expr
  ;

andExpression
  : notExpression (AND notExpression)*  // expr 🤝 expr
  ;

notExpression
  : NOT? comparisonExpression  // ⛔ expr
  ;

comparisonExpression
  : additiveExpression ((DOUBLE_EQUAL | NOTEQUAL | LESS | LEQ | GREATER | GEQ) additiveExpression)?
  ;

additiveExpression
  : multiplicativeExpression ((PLUS | MINUS) multiplicativeExpression)*
  ;

multiplicativeExpression
  : unaryExpression ((MULTIPLY | DIVIDE) unaryExpression)*
  ;

unaryExpression
  : (MINUS)? primaryExpression
  ;

primaryExpression
  : INT_VALUE                                   // Integer value
  | STRING_VALUE                                // String value
  | CHAR_VALUE                                  // Character value
  | TRUE                                        // ✅ (true)
  | FALSE                                       // ❌ (false)
  | NOT primaryExpression                       // ⛔ expr (negation)
  | tupleValue                                  // Tuple value
  | EMOJI_ID                                    // Emoji identifier
  | functionCall                                // Function call
  | leftExpression                              // Left expression
  | LEFT_PARENTHESIS expression RIGHT_PARENTHESIS // Parenthesized expression
  ;

tupleValue
  : LEFT_PARENTHESIS expression COMMA expression RIGHT_PARENTHESIS
  ;


//   Structure for grouping
block
  : LEFT_BRACE statement* RIGHT_BRACE
  ;