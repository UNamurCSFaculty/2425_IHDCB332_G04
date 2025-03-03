parser grammar EMJParser;

// Indique que ce parser utilise les tokens définis dans EMJLexer.g4
options { tokenVocab = EMJLexer; }

//------------------------------------------------------------------------------
// 1) root
//   Règle racine (point d'entrée).
//   Obligatoire: Permet de distinguer si le fichier à parser est .map (mapFile) ou .moj (programFile).
//   EOF : fin de fichier (= End Of File).
root
  : comment* (mapFile | programFile) comment* EOF
  ;

//------------------------------------------------------------------------------
// 2) mapFile (.map)
//   Obligatoire: Un fichier .map doit commencer par "with L, C, orientation"
//   Puis au moins une ligne de map (mapRow).
//   L et C sont des entiers (INT_VALUE).
//   orientation correspond à un emoji (UP_ARROW, RIGHT_ARROW, etc.).
//------------------------------------------------------------------------------
mapFile
  : MAP WITH INT_VALUE COMMA INT_VALUE COMMA orientation SEMICOLON mapCell+
  ;

// orientation : défini l'emoji de direction initiale (nord, sud, est ou ouest).
orientation
  : UP_ARROW
  | RIGHT_ARROW
  | DOWN_ARROW
  | LEFT_ARROW
  ;

// mapCell : le contenu d'une case (police, route, obstacle, voleur).
//   Obligatoire pour représenter chaque case.
mapCell
  : COP
  | ROAD
  | OBSTACLE
  | THIEF
  ;

//------------------------------------------------------------------------------
// 3) programFile (.moj)
//   Fichier de programme. Selon l'énoncé,
//   on peut avoir : un import (optionnel ou obligatoire selon le projet),
//                  une mainFunction (souvent obligatoire),
//                  des déclarations de fonctions (facultatives),
//                  et des statements.
//------------------------------------------------------------------------------
programFile
  : importStatement?        // Bonus ou obligatoire (selon consignes du projet)
    mainFunction?           // Souvent obligatoire, si le cahier des charges exige "main"
    functionDecl*           // Bonus: fonctions additionnelles
    statement*              // Différentes instructions
  ;

// importStatement : instruction d'import (ex. 📦 "maCarte.map").
//   Souvent, ce n'est pas terminé par un ';' selon l'énoncé.
importStatement
  : PACKAGE STRING_VALUE SEMICOLON?
  ;

// Enumeration des différents types possibles
// Correspond à n'importe quel type
type
  : INT_TYPE|BOOL_TYPE|CHAR_TYPE|STRING_TYPE|TUPLE_TYPE|VOID_TYPE
  ;

tupleType
  : TUPLE_TYPE LEFT_PARENTHESIS (INT_TYPE | BOOL_TYPE | CHAR_TYPE | STRING_TYPE) RIGHT_PARENTHESIS
  ;
// mainFunction : la fonction principale.
//   Souvent obligatoire dans un langage similaire à C/Java.
//   Le type est forcément void
//   Elle est représentée par l'emoji MAIN (🏠) + bloc.
mainFunction
  : VOID_TYPE MAIN block
  ;

// functionDecl : déclaration de fonctions supplémentaires (bonus).
//   type ou INT_TYPE, un identifiant emoji, paramList optionnelle, un bloc.
functionDecl
  : type EMOJI_ID optionalParamList block
  ;

optionalParamList
  : LEFT_PARENTHESIS paramList? RIGHT_PARENTHESIS
  ;

// paramList : ensemble de paramètres séparés par des virgules.
paramList
  : param (COMMA param)*
  ;

// param : ex. 🔢 [x] ou autre type + identifiant.
param
  : type EMOJI_ID
  ;

//------------------------------------------------------------------------------
// 4) statement
//   Liste des instructions possibles dans le .moj.
//   Plusieurs sont "obligatoires" si le projet l’exige, d'autres "bonus" si non imposées.
//------------------------------------------------------------------------------
statement
  : varDecl SEMICOLON         // Déclaration de variable
  | assignment SEMICOLON      // Affectation
  | functionCallStmt SEMICOLON
  | predefinedStmt SEMICOLON
  | ifStatement               // Conditionnelle if/else
  | loopStatement             // Boucles
  | returnStatement SEMICOLON // Retour de fonction
  ;

predefinedStmt
  : STOP_THIEF LEFT_PARENTHESIS RIGHT_PARENTHESIS
  | SOUND_TOGGLE LEFT_PARENTHESIS RIGHT_PARENTHESIS
  | LIGHT_TOGGLE LEFT_PARENTHESIS RIGHT_PARENTHESIS
  | UP_ARROW LEFT_PARENTHESIS expression RIGHT_PARENTHESIS
  | DOWN_ARROW LEFT_PARENTHESIS expression RIGHT_PARENTHESIS
  | RIGHT_ARROW LEFT_PARENTHESIS expression RIGHT_PARENTHESIS
  | LEFT_ARROW LEFT_PARENTHESIS expression RIGHT_PARENTHESIS
  ;

varDecl
  : type EMOJI_ID (EQUAL expression)?
  ;

assignment
  : EMOJI_ID EQUAL expression
  ;

leftExpression
  : EMOJI_ID
  | EMOJI_ID TUPLE_FIRST
  | EMOJI_ID TUPLE_SECOND
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
    (ELSE block)?
  ;

loopStatement
  : WHILE LEFT_PARENTHESIS expression RIGHT_PARENTHESIS block
  | FOR LEFT_PARENTHESIS INT_VALUE RIGHT_PARENTHESIS block
  ;

// returnStatement : ex. ↩️ expression?
//   Bonus si on a des fonctions qui renvoient quelque chose.
returnStatement
  : RETURN expression?
  ;

//------------------------------------------------------------------------------
// 5) expression
//   Gère la logique (ET/OU), les comparaisons, l’arithmétique, etc.
//   Obligatoire si le langage manipule des calculs ou booléens.
//------------------------------------------------------------------------------
expression
  : orExpression
  ;

orExpression
  : andExpression (OR andExpression)*
  ;

andExpression
  : notExpression (AND notExpression)*
  ;

notExpression
  : NOT? comparisonExpression
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
  : INT_VALUE
  | STRING_VALUE
  | CHAR_VALUE
  | TRUE
  | FALSE
  | tupleValue
  | functionCall
  | leftExpression
  | LEFT_PARENTHESIS expression RIGHT_PARENTHESIS
  ;

// Ajout de tupleValue pour gérer les tuples
tupleValue
  : LEFT_PARENTHESIS expression COMMA expression RIGHT_PARENTHESIS
  ;


//------------------------------------------------------------------------------
// 6) block
//   Un bloc { ... } pour regrouper des statements (ex: dans main, dans if, etc.).
//   Obligatoire si la syntaxe du projet l’exige pour structurer le code.
//------------------------------------------------------------------------------
block
  : LEFT_BRACE statement* RIGHT_BRACE
  ;

//------------------------------------------------------------------------------
// 7) comment
//   Un commentaire peut avoir 2 formes :
//      - uniligne -> (loudspeaker, U+1F4E2) au début de la ligne, texte après
//      - multiligne -> (speaker-high-volume, U+1F50A) au début du commentaire
//                      (speaker-low-volume,  U+1F508) à la fin du commentaire
//------------------------------------------------------------------------------
comment
  : BEGIN_COM COMMENT_CONTENT* END_COM
  | ONE_LINE_COM
  ;