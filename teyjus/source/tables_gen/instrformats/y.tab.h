/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_YY_Y_TAB_H_INCLUDED
# define YY_YY_Y_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    OPTYPES = 258,
    INSTRCAT = 259,
    INSTRUCTIONS = 260,
    OPCODE = 261,
    MAXOPERAND = 262,
    CALL_I1_LEN = 263,
    SEMICOLON = 264,
    ERROR = 265,
    LBRACKET = 266,
    RBRACKET = 267,
    ID = 268,
    NUM = 269,
    STRING = 270,
    STRING2 = 271
  };
#endif
/* Tokens.  */
#define OPTYPES 258
#define INSTRCAT 259
#define INSTRUCTIONS 260
#define OPCODE 261
#define MAXOPERAND 262
#define CALL_I1_LEN 263
#define SEMICOLON 264
#define ERROR 265
#define LBRACKET 266
#define RBRACKET 267
#define ID 268
#define NUM 269
#define STRING 270
#define STRING2 271

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 38 "instrformats.y" /* yacc.c:1909  */

    char*    name;
    char*    text;
    struct
    {
        int    ival;
        char*  sval;
    }        isval;

#line 96 "y.tab.h" /* yacc.c:1909  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_Y_TAB_H_INCLUDED  */
