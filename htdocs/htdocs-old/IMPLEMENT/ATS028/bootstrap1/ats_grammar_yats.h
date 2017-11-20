/* A Bison parser, made by GNU Bison 2.4.3.  */

/* Skeleton interface for Bison's Yacc-like parsers in C
   
      Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006,
   2009, 2010 Free Software Foundation, Inc.
   
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


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     YYBEG_i0de = 258,
     YYBEG_s0rtid = 259,
     YYBEG_si0de = 260,
     YYBEG_di0de = 261,
     YYBEG_s0exp = 262,
     YYBEG_d0exp = 263,
     YYBEG_d0ecseq_sta = 264,
     YYBEG_d0ecseq_dyn = 265,
     TOKEN_eof = 266,
     LITERAL_char = 267,
     LITERAL_extcode = 268,
     LITERAL_float = 269,
     LITERAL_floatsp = 270,
     LITERAL_int = 271,
     LITERAL_intsp = 272,
     LITERAL_string = 273,
     IDENTIFIER_alp = 274,
     IDENTIFIER_sym = 275,
     IDENTIFIER_arr = 276,
     IDENTIFIER_tmp = 277,
     IDENTIFIER_ext = 278,
     IDENTIFIER_dlr = 279,
     IDENTIFIER_srp = 280,
     ABSPROP = 281,
     ABSTYPE = 282,
     ABST0YPE = 283,
     ABSVIEW = 284,
     ABSVIEWTYPE = 285,
     ABSVIEWT0YPE = 286,
     AND = 287,
     AS = 288,
     ASSUME = 289,
     ATLAM = 290,
     ATLLAM = 291,
     ATFIX = 292,
     BEGIN = 293,
     BREAK = 294,
     CASE = 295,
     CASEMINUS = 296,
     CASEPLUS = 297,
     CASTFN = 298,
     CLASSDEC = 299,
     CONTINUE = 300,
     DATASORT = 301,
     DATAPARASORT = 302,
     DATAPROP = 303,
     DATATYPE = 304,
     DATAVIEW = 305,
     DATAVIEWTYPE = 306,
     DO = 307,
     DYN = 308,
     DYNLOAD = 309,
     ELSE = 310,
     END = 311,
     EXCEPTION = 312,
     EXTERN = 313,
     FIX = 314,
     FN = 315,
     FNSTAR = 316,
     FOR = 317,
     FORSTAR = 318,
     FUN = 319,
     IF = 320,
     IMPLEMENT = 321,
     IN = 322,
     INFIX = 323,
     INFIXL = 324,
     INFIXR = 325,
     LAM = 326,
     LET = 327,
     LLAM = 328,
     LOCAL = 329,
     MACDEF = 330,
     MACRODEF = 331,
     NONFIX = 332,
     OF = 333,
     OP = 334,
     OVERLOAD = 335,
     PAR = 336,
     POSTFIX = 337,
     PRAXI = 338,
     PREFIX = 339,
     PRFN = 340,
     PRFUN = 341,
     PROPDEF = 342,
     PROPMINUS = 343,
     PROPPLUS = 344,
     PRVAL = 345,
     REC = 346,
     R0EAD = 347,
     SCASE = 348,
     SIF = 349,
     SORTDEF = 350,
     STACST = 351,
     STADEF = 352,
     STAIF = 353,
     STALOAD = 354,
     STAVAR = 355,
     SYMELIM = 356,
     SYMINTR = 357,
     THEN = 358,
     TRY = 359,
     TYPEDEF = 360,
     TYPEMINUS = 361,
     TYPEPLUS = 362,
     T0YPE = 363,
     T0YPEMINUS = 364,
     T0YPEPLUS = 365,
     VAL = 366,
     VALMINUS = 367,
     VALPLUS = 368,
     VAR = 369,
     VIEWDEF = 370,
     VIEWMINUS = 371,
     VIEWPLUS = 372,
     VIEWTYPEDEF = 373,
     VIEWTYPEMINUS = 374,
     VIEWTYPEPLUS = 375,
     VIEWT0YPE = 376,
     VIEWT0YPEMINUS = 377,
     VIEWT0YPEPLUS = 378,
     WHEN = 379,
     WHERE = 380,
     WHILE = 381,
     WHILESTAR = 382,
     WITH = 383,
     WITHPROP = 384,
     WITHTYPE = 385,
     WITHVIEW = 386,
     WITHVIEWTYPE = 387,
     AMPERSAND = 388,
     BACKQUOTE = 389,
     BACKSLASH = 390,
     BANG = 391,
     BAR = 392,
     COMMA = 393,
     COLON = 394,
     SEMICOLON = 395,
     DOT = 396,
     EQ = 397,
     LT = 398,
     GT = 399,
     DOLLAR = 400,
     HASH = 401,
     TILDE = 402,
     DOTDOT = 403,
     DOTDOTDOT = 404,
     EQLT = 405,
     EQGT = 406,
     EQLTGT = 407,
     EQGTGT = 408,
     EQSLASHEQGT = 409,
     EQSLASHEQGTGT = 410,
     GTLT = 411,
     DOTLT = 412,
     GTDOT = 413,
     DOTLTGTDOT = 414,
     MINUSLT = 415,
     MINUSGT = 416,
     MINUSLTGT = 417,
     COLONLT = 418,
     COLONLTGT = 419,
     BACKQUOTELPAREN = 420,
     COMMALPAREN = 421,
     PERCENTLPAREN = 422,
     DLRARRSZ = 423,
     DLRLST_T = 424,
     DLRLST_VT = 425,
     DLRREC_T = 426,
     DLRREC_VT = 427,
     DLRTUP_T = 428,
     DLRTUP_VT = 429,
     DLRDELAY = 430,
     DLRLDELAY = 431,
     DLRDYNLOAD = 432,
     DLREFFMASK_ALL = 433,
     DLREFFMASK_EXN = 434,
     DLREFFMASK_NTM = 435,
     DLREFFMASK_REF = 436,
     DLRDECRYPT = 437,
     DLRENCRYPT = 438,
     DLREXTERN = 439,
     DLREXTVAL = 440,
     DLREXTYPE = 441,
     DLREXTYPE_STRUCT = 442,
     DLRFOLD = 443,
     DLRUNFOLD = 444,
     DLRRAISE = 445,
     DLRTYPEOF = 446,
     SRPFILENAME = 447,
     SRPLOCATION = 448,
     SRPCHARCOUNT = 449,
     SRPLINECOUNT = 450,
     SRPASSERT = 451,
     SRPDEFINE = 452,
     SRPELSE = 453,
     SRPELIF = 454,
     SRPELIFDEF = 455,
     SRPELIFNDEF = 456,
     SRPENDIF = 457,
     SRPERROR = 458,
     SRPIF = 459,
     SRPIFDEF = 460,
     SRPIFNDEF = 461,
     SRPINCLUDE = 462,
     SRPPRINT = 463,
     SRPTHEN = 464,
     SRPUNDEF = 465,
     FOLDAT = 466,
     FREEAT = 467,
     VIEWAT = 468,
     LPAREN = 469,
     RPAREN = 470,
     LBRACKET = 471,
     RBRACKET = 472,
     LBRACE = 473,
     RBRACE = 474,
     ATLPAREN = 475,
     ATLBRACKET = 476,
     ATLBRACE = 477,
     QUOTELPAREN = 478,
     QUOTELBRACKET = 479,
     QUOTELBRACE = 480,
     HASHLPAREN = 481,
     HASHLBRACKET = 482,
     HASHLBRACE = 483,
     PATAS = 484,
     PATFREE = 485,
     SEXPLAM = 486,
     DEXPLAM = 487,
     DEXPFIX = 488,
     CLAUS = 489,
     DEXPCASE = 490,
     DEXPIF = 491,
     DEXPRAISE = 492,
     DEXPTRY = 493,
     DEXPFOR = 494,
     DEXPWHILE = 495,
     BARCLAUSSEQNONE = 496,
     TMPSEXP = 497,
     TMPSARG = 498,
     SARRIND = 499,
     SEXPDARGSEQEMPTY = 500
   };
#endif



#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif

extern YYSTYPE yylval;


