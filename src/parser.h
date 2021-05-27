/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton interface for Bison's Yacc-like parsers in C

   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor,
   Boston, MA 02110-1301, USA.  */

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

/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     LPAREN = 258,
     RPAREN = 259,
     LBRACKET = 260,
     RBRACKET = 261,
     SET_LOGIC = 262,
     GET_MODEL = 263,
     ASSERT = 264,
     CHECK_SAT = 265,
     DECLARE_FUN = 266,
     EXIT = 267,
     GET_ASSIGNMENT = 268,
     LET = 269,
     NUMERAL = 270,
     SYMBOL = 271,
     BOOL = 272,
     INT = 273,
     SAT = 274,
     UNSAT = 275,
     UNKNOWN = 276,
     SOURCE = 277,
     TRUE_TOK = 278,
     FALSE_TOK = 279,
     ITE = 280,
     NOT = 281,
     AND = 282,
     EQUAL = 283,
     OR = 284,
     GE = 285,
     LE = 286,
     LARGE = 287,
     SMALL = 288,
     REPRESENT = 289,
     MINUS = 290,
     PLUS = 291,
     MUL = 292,
     SETVERSION = 293,
     SETCATEGORY = 294,
     SETSOURCE = 295,
     SETSTATUS = 296,
     IMPLY = 297,
     LIST = 298,
     ANDORLIST = 299,
     LETLIST = 300,
     LETTERM = 301,
     ITELIST = 302
   };
#endif
/* Tokens.  */
#define LPAREN 258
#define RPAREN 259
#define LBRACKET 260
#define RBRACKET 261
#define SET_LOGIC 262
#define GET_MODEL 263
#define ASSERT 264
#define CHECK_SAT 265
#define DECLARE_FUN 266
#define EXIT 267
#define GET_ASSIGNMENT 268
#define LET 269
#define NUMERAL 270
#define SYMBOL 271
#define BOOL 272
#define INT 273
#define SAT 274
#define UNSAT 275
#define UNKNOWN 276
#define SOURCE 277
#define TRUE_TOK 278
#define FALSE_TOK 279
#define ITE 280
#define NOT 281
#define AND 282
#define EQUAL 283
#define OR 284
#define GE 285
#define LE 286
#define LARGE 287
#define SMALL 288
#define REPRESENT 289
#define MINUS 290
#define PLUS 291
#define MUL 292
#define SETVERSION 293
#define SETCATEGORY 294
#define SETSOURCE 295
#define SETSTATUS 296
#define IMPLY 297
#define LIST 298
#define ANDORLIST 299
#define LETLIST 300
#define LETTERM 301
#define ITELIST 302




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef int YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE yylval;

