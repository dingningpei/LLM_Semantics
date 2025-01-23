/* A Bison parser, made by GNU Bison 2.7.12-4996.  */

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

#ifndef YY_YY_FLATZINC_PARSER_TAB_H_INCLUDED
# define YY_YY_FLATZINC_PARSER_TAB_H_INCLUDED
/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     INT_LIT = 258,
     BOOL_LIT = 259,
     FLOAT_LIT = 260,
     ID = 261,
     STRING_LIT = 262,
     VAR = 263,
     PAR = 264,
     ANNOTATION = 265,
     ANY = 266,
     ARRAY = 267,
     BOOL = 268,
     CASE = 269,
     COLONCOLON = 270,
     CONSTRAINT = 271,
     DEFAULT = 272,
     DOTDOT = 273,
     ELSE = 274,
     ELSEIF = 275,
     ENDIF = 276,
     ENUM = 277,
     FLOAT = 278,
     FUNCTION = 279,
     IF = 280,
     INCLUDE = 281,
     INT = 282,
     LET = 283,
     MAXIMIZE = 284,
     MINIMIZE = 285,
     OF = 286,
     SATISFY = 287,
     OUTPUT = 288,
     PREDICATE = 289,
     RECORD = 290,
     SET = 291,
     SHOW = 292,
     SHOWCOND = 293,
     SOLVE = 294,
     STRING = 295,
     TEST = 296,
     THEN = 297,
     TUPLE = 298,
     TYPE = 299,
     VARIANT_RECORD = 300,
     WHERE = 301
   };
#endif


#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
{
/* Line 2053 of yacc.c  */
#line 365 "flatzinc/parser.yxx"
 int iValue; char* sValue; bool bValue; double dValue;
         std::vector<int>* setValue;
         FlatZinc::AST::SetLit* setLit;
         std::vector<double>* floatSetValue;
         std::vector<FlatZinc::AST::SetLit>* setValueList;
         FlatZinc::Option<FlatZinc::AST::SetLit* > oSet;
         FlatZinc::VarSpec* varSpec;
         FlatZinc::Option<FlatZinc::AST::Node*> oArg;
         std::vector<FlatZinc::VarSpec*>* varSpecVec;
         FlatZinc::Option<std::vector<FlatZinc::VarSpec*>* > oVarSpecVec;
         FlatZinc::AST::Node* arg;
         FlatZinc::AST::Array* argVec;
       

/* Line 2053 of yacc.c  */
#line 118 "flatzinc/parser.tab.h"
} YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif


#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void *parm);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */

#endif /* !YY_YY_FLATZINC_PARSER_TAB_H_INCLUDED  */
