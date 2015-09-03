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
    LBRACKET = 258,
    RBRACKET = 259,
    LPAREN = 260,
    RPAREN = 261,
    COMMA = 262,
    POUND = 263,
    SEMICOLON = 264,
    TRUE = 265,
    FALSE = 266,
    TYARROW = 267,
    TYAPP = 268,
    INFIX = 269,
    INFIXL = 270,
    INFIXR = 271,
    PREFIX = 272,
    PREFIXR = 273,
    POSTFIX = 274,
    POSTFIXL = 275,
    NOFIXITY = 276,
    MIN1 = 277,
    MIN2 = 278,
    MAX = 279,
    NOCODE = 280,
    LSSYMB = 281,
    LSSTART = 282,
    LSEND = 283,
    PREDSYMB = 284,
    PREDSTART = 285,
    PREDEND = 286,
    REGCL = 287,
    BACKTRACK = 288,
    KIND = 289,
    CONST = 290,
    EMPTY = 291,
    TYSKEL = 292,
    TYPE = 293,
    EMPTYTYPE = 294,
    ERROR = 295,
    ID = 296,
    NUM = 297,
    STRING = 298
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 42 "pervasives.y" /* yacc.c:1909  */

    char*            name;  
    char*            text;
    OP_Fixity        fixityType;
    OP_Prec          precType;
    OP_Code          codeType;
    UTIL_Bool        boolType;
    struct 
    {
        int   ival;
        char* sval;
    }                isval;
    Type             tyval;
    TypeList         tylistval;

#line 114 "y.tab.h" /* yacc.c:1909  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_Y_TAB_H_INCLUDED  */
