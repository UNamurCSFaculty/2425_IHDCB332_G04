parser grammar EMJParser;

options { tokenVocab = EMJLexer; }

// parser root, everything must start from here
root : test EOF;

test : left EQUAL right SEMICOLON;

left : INT_TYPE EMOJI_ID;

right : INT_VALUE;