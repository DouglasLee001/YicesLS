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
     DISTINCT = 284,
     OR = 285,
     GE = 286,
     LE = 287,
     LARGE = 288,
     SMALL = 289,
     REPRESENT = 290,
     MINUS = 291,
     PLUS = 292,
     MUL = 293,
     SETVERSION = 294,
     SETCATEGORY = 295,
     SETSOURCE = 296,
     SETLICENSE = 297,
     SETMODEL = 298,
     SETSTATUS = 299,
     IMPLY = 300,
     SETPRINT = 301,
     LIST = 302,
     ANDORLIST = 303,
     LETLIST = 304,
     LETTERM = 305,
     ITELIST = 306
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
#define DISTINCT 284
#define OR 285
#define GE 286
#define LE 287
#define LARGE 288
#define SMALL 289
#define REPRESENT 290
#define MINUS 291
#define PLUS 292
#define MUL 293
#define SETVERSION 294
#define SETCATEGORY 295
#define SETSOURCE 296
#define SETLICENSE 297
#define SETMODEL 298
#define SETSTATUS 299
#define IMPLY 300
#define SETPRINT 301
#define LIST 302
#define ANDORLIST 303
#define LETLIST 304
#define LETTERM 305
#define ITELIST 306




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef int YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE yylval;

