parser grammar EMJParser;

// Indique que ce parser utilise les tokens définis dans EMJLexer.g4
options { tokenVocab = EMJLexer; }

//------------------------------------------------------------------------------
// 1) root
//   Règle racine (point d'entrée).
//   Obligatoire: Permet de distinguer si le fichier à parser est .map (mapFile) ou .moj (programFile).
//   EOF : fin de fichier.
root
  : (mapFile | programFile) EOF
  ;

//------------------------------------------------------------------------------
// 2) mapFile (.map)
//   Obligatoire: Un fichier .map doit commencer par "with L, C, orientation"
//   Puis au moins une ligne de map (mapRow).
//   L et C sont des entiers (INT_VALUE).
//   orientation correspond à un emoji (UP_ARROW, RIGHT_ARROW, etc.).
//------------------------------------------------------------------------------
mapFile
  : WITH INT_VALUE COMMA INT_VALUE COMMA orientation mapRow+
  ;

// orientation : défini l'emoji de direction initiale (nord, sud, est ou ouest).
orientation
  : UP_ARROW
  | RIGHT_ARROW
  | DOWN_ARROW
  | LEFT_ARROW
  ;

// mapRow : une ligne dans la carte.
//   (mapCell)+ signifie qu’il y a au moins une cellule par ligne.
mapRow
  : mapCell+
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
  | functionCall SEMICOLON    // Appel de fonction "inutile" (pas de retour stocké)
  | ifStatement               // Conditionnelle if/else
  | loopStatement             // Boucles
  | returnStatement SEMICOLON // Retour de fonction
  ;

// varDecl : Déclaration d’une variable, par ex. 🔢 [v] = 10;
//   Obligatoire si on veut gérer des variables.
varDecl
  : intDecl|stringDecl|boolDecl|charDecl|tupleDecl
  ;

// String a = "aaaaaa"
stringDecl
  : STRING_TYPE EMOJI_ID (EQUAL STRING_VALUE)?
  ;
