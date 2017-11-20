

// preamble

%{^
#include "ats_grammar_yats.h"
%} // end of ...

(* ****** ****** *)

staload "libats_lex_lexing.sats"

(* ****** ****** *)

staload CS = "ats_charlst.sats"
staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload Loc = "ats_location.sats"
staload POSMARK = "ats_posmark.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_lexer.sats"

(* ****** ****** *)

overload prerr with $Loc.prerr_location

(* ****** ****** *)
//
// HX: it is called when [ats_lexer_lats.dats] is loaded dynamically
//
val () = ats_lexer_lats_initialize () where {
  extern fun ats_lexer_lats_initialize (): void = "ats_lexer_lats_initialize"
} // end of [val]

(* ****** ****** *)

dataviewtype
poslst = (* list of positions *)
  | POSLSTnil | POSLSTcons of (position_t, poslst)
// end of [poslst]

fun poslst_free (ps: poslst): void = case+ ps of
  | ~POSLSTcons (p, ps) => poslst_free ps | ~POSLSTnil () => ()
// end of [poslst_free]

extern
fun keyword_search (name: string): token_t
  = "atsopt_keyword_search" // implemented in C in [ats_keyword.dats]
// end of [keyword_search]

//

fn MAIN_lexing_error (): token_t = lexing_error ()

//

extern fun CHAR (fstpos: position_t): token_t

fn CHAR_lexing_error (fstpos: position_t): token_t = lexing_error ()
fn CHAR0 (): token_t = CHAR (lexing_fstpos_get ())

(* ****** ****** *)

extern fun COMMENT (p: position_t, ps: poslst): void

fn COMMENT_lexing_error
  (p: position_t, ps: poslst): void =
  let val () = poslst_free (ps) in lexing_error () end
// end of [COMMENT_lexing_error]

fn COMMENT0 (): void = let
  val fstpos = lexing_fstpos_get ()
  val fstoff = position_toff fstpos
  val () = $POSMARK.posmark_insert_comment_beg fstoff
in
  COMMENT (fstpos, POSLSTnil ())
end // end of [COMMENT0]

(* ****** ****** *)

extern fun COMMENT_CLIKE (p: position_t): void

fn COMMENT_CLIKE_lexing_error
  (p: position_t): void = lexing_error ()
// end of [COMMENT_CLIKE_lexing_error]

fn COMMENT0_CLIKE (): void = let
  val fstpos = lexing_fstpos_get ()
  val fstoff = position_toff fstpos
  val () = $POSMARK.posmark_insert_comment_beg fstoff
in
  COMMENT_CLIKE (fstpos)
end // end of [COMMENT0_CLIKE]

(* ****** ****** *)

extern fun COMMENT_LINE (): void
fn COMMENT_LINE_lexing_error (): void = lexing_error ()

extern fun COMMENT_REST (): void
fn COMMENT_REST_lexing_error (): void = lexing_error ()

(* ****** ****** *)

extern fun STRING {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): token_t

fn STRING_lexing_error {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): token_t =
  ($CS.charlst_free cs; lexing_error ())
// end of [STRING_lexing_error]

fn STRING0 (): token_t =
  STRING (lexing_fstpos_get (), $CS.CHARLSTnil (), 0)
// end of [STRING0]

(* ****** ****** *)

extern fun EXTCODE {n:nat}
  (fstpos: position_t, i: int, cs: $CS.charlst_vt n, n: int n): token_t

fn EXTCODE_lexing_error {n:nat}
  (fstpos: position_t, i: int, cs: $CS.charlst_vt n, n: int n): token_t =
  ($CS.charlst_free cs; lexing_error ())
// end of [EXTCODE_lexing_error]

fn EXTCODE0 (i: int): token_t =
  EXTCODE (lexing_fstpos_get (), i, $CS.CHARLSTnil (), 0)
// end of [EXTCODE0]

(* ****** ****** *)

implement ISNONE = $extval (token_t, "-1")
implement ISSTATIC = $extval (token_t, "ISSTATIC")
implement ISDYNAMIC = $extval (token_t, "ISDYNAMIC")

%{$
ats_bool_type
eq_token_token
  (ats_int_type tok1, ats_int_type tok2) {
  return (tok1 == tok2 ? ats_true_bool : ats_false_bool) ;
} // end of [ats_bool_type eq_token_token]
%} // end of ...

//

macdef TOKEN_eof = $extval (token_t, "TOKEN_eof")

//

macdef LITERAL_char = $extval (token_t, "LITERAL_char")
macdef LITERAL_float = $extval (token_t, "LITERAL_float")
macdef LITERAL_floatsp = $extval (token_t, "LITERAL_floatsp")
macdef LITERAL_int = $extval (token_t, "LITERAL_int")
macdef LITERAL_intsp = $extval (token_t, "LITERAL_intsp")
macdef LITERAL_string = $extval (token_t, "LITERAL_string")

macdef LITERAL_extcode = $extval (token_t, "LITERAL_extcode")

macdef IDENTIFIER_alp = $extval (token_t, "IDENTIFIER_alp")
macdef IDENTIFIER_sym = $extval (token_t, "IDENTIFIER_sym")
macdef IDENTIFIER_arr = $extval (token_t, "IDENTIFIER_arr")
macdef IDENTIFIER_tmp = $extval (token_t, "IDENTIFIER_tmp")

macdef IDENTIFIER_dlr = $extval (token_t, "IDENTIFIER_dlr")
macdef IDENTIFIER_srp = $extval (token_t, "IDENTIFIER_srp")

macdef IDENTIFIER_ext = $extval (token_t, "IDENTIFIER_ext")

//

macdef ABSPROP = $extval (token_t, "ABSPROP")
macdef ABSTYPE = $extval (token_t, "ABSTYPE")
macdef ABST0YPE = $extval (token_t, "ABST0YPE")
macdef ABSVIEW = $extval (token_t, "ABSVIEW")
macdef ABSVIEWTYPE = $extval (token_t, "ABSVIEWTYPE")
macdef ABSVIEWT0YPE = $extval (token_t, "ABSVIEWT0YPE")
macdef AND = $extval (token_t, "AND")
macdef AS = $extval (token_t, "AS")
macdef ASSUME = $extval (token_t, "ASSUME")
macdef ATLAM = $extval (token_t, "ATLAM")
macdef ATLLAM = $extval (token_t, "ATLLAM")
macdef ATFIX = $extval (token_t, "ATFIX")
macdef BEGIN = $extval (token_t, "BEGIN")
macdef BREAK = $extval (token_t, "BREAK")
macdef CASE = $extval (token_t, "CASE")
macdef CASEMINUS = $extval (token_t, "CASEMINUS")
macdef CASEPLUS = $extval (token_t, "CASEPLUS")
macdef CLASS = $extval (token_t, "CLASS")
macdef CONTINUE = $extval (token_t, "CONTINUE")
macdef DATASORT = $extval (token_t, "DATASORT")
macdef DATAPARASORT = $extval (token_t, "DATAPARASORT")
macdef DATAPROP = $extval (token_t, "DATAPROP")
macdef DATATYPE = $extval (token_t, "DATATYPE")
macdef DATAVIEW = $extval (token_t, "DATAVIEW")
macdef DATAVIEWTYPE = $extval (token_t, "DATAVIEWTYPE")
macdef DYNLOAD = $extval (token_t, "DYNLOAD")
macdef ELSE = $extval (token_t, "ELSE")
macdef END = $extval (token_t, "END")
macdef EXCEPTION = $extval (token_t, "EXCEPTION")
macdef EXTERN = $extval (token_t, "EXTERN")
macdef FN = $extval (token_t, "FN")
macdef FNSTAR = $extval (token_t, "FNSTAR")
macdef FOR = $extval (token_t, "FOR")
macdef FORSTAR = $extval (token_t, "FORSTAR")
macdef FUN = $extval (token_t, "FUN")
macdef FIX = $extval (token_t, "FIX")
macdef IF = $extval (token_t, "IF")
macdef IMPLEMENT = $extval (token_t, "IMPLEMENT")
macdef IN = $extval (token_t, "IN")
macdef INFIX = $extval (token_t, "INFIX")
macdef INFIXL = $extval (token_t, "INFIXL")
macdef INFIXR = $extval (token_t, "INFIXR")
macdef LAM = $extval (token_t, "LAM")
macdef LET = $extval (token_t, "LET")
macdef LLAM = $extval (token_t, "LLAM")
macdef LOCAL = $extval (token_t, "LOCAL")
macdef MACDEF = $extval (token_t, "MACDEF")
macdef MACRODEF = $extval (token_t, "MACRODEF")
(*
macdef METHOD = $extval (token_t, "METHOD")
macdef METHODSTAR = $extval (token_t, "METHODSTAR")
macdef MODCLS = $extval (token_t, "MODCLS")
*)
macdef MODPROP = $extval (token_t, "MODPROP")
macdef MODTYPE = $extval (token_t, "MODTYPE")
macdef MODULE = $extval (token_t, "MODULE")
macdef NONFIX = $extval (token_t, "NONFIX")
macdef OVERLOAD = $extval (token_t, "OVERLOAD")
macdef POSTFIX = $extval (token_t, "POSTFIX")
macdef PRAXI = $extval (token_t, "PRAXI")
macdef PRFIX = $extval (token_t, "PRFIX")
macdef PRFN = $extval (token_t, "PRFN")
macdef PRFUN = $extval (token_t, "PRFUN")
macdef PROPMINUS = $extval (token_t, "PROPMINUS")
macdef PROPPLUS = $extval (token_t, "PROPPLUS")
macdef PRVAL = $extval (token_t, "PRVAL")
(*
macdef OBJECT = $extval (token_t, "OBJECT")
macdef OBJCLS = $extval (token_t, "OBJCLS")
*)
macdef OF = $extval (token_t, "OF")
macdef OP = $extval (token_t, "OP")
macdef PROPDEF = $extval (token_t, "PROPDEF")
macdef R0EAD = $extval (token_t, "R0EAD")
macdef REC = $extval (token_t, "REC")
macdef STAIF = $extval (token_t, "STAIF")
macdef SORTDEF = $extval (token_t, "SORTDEF")
macdef STA = $extval (token_t, "STA")
macdef STADEF = $extval (token_t, "STADEF")
macdef STALOAD = $extval (token_t, "STALOAD")
macdef STAVAR = $extval (token_t, "STAVAR")
(*
macdef STRUCT = $extval (token_t, "STRUCT")
*)
macdef SYMELIM = $extval (token_t, "SYMELIM")
macdef SYMINTR = $extval (token_t, "SYMINTR")
macdef THEN = $extval (token_t, "THEN")
macdef TRY = $extval (token_t, "TRY")
macdef TYPEDEF = $extval (token_t, "TYPEDEF")
macdef TYPEMINUS = $extval (token_t, "TYPEMINUS")
macdef TYPEPLUS = $extval (token_t, "TYPEPLUS")
macdef T0YPE = $extval (token_t, "T0YPE")
macdef T0YPEMINUS = $extval (token_t, "T0YPEMINUS")
macdef T0YPEPLUS = $extval (token_t, "T0YPEPLUS")
(*
macdef UNION = $extval (token_t, "UNION")
*)
macdef VAL = $extval (token_t, "VAL")
macdef VALMINUS = $extval (token_t, "VALMINUS")
macdef VALPLUS = $extval (token_t, "VALPLUS")
macdef VAR = $extval (token_t, "VAR")
macdef VIEWDEF = $extval (token_t, "VIEWDEF")
macdef VIEWMINUS = $extval (token_t, "VIEWMINUS")
macdef VIEWPLUS = $extval (token_t, "VIEWPLUS")
macdef VIEWTYPEDEF = $extval (token_t, "VIEWTYPEDEF")
macdef VIEWTYPEMINUS = $extval (token_t, "VIEWTYPEMINUS")
macdef VIEWTYPEPLUS = $extval (token_t, "VIEWTYPEPLUS")
macdef VIEWT0YPE = $extval (token_t, "VIEWT0YPE")
macdef VIEWT0YPEMINUS = $extval (token_t, "VIEWT0YPEMINUS")
macdef VIEWT0YPEPLUS = $extval (token_t, "VIEWT0YPEPLUS")
macdef WHEN = $extval (token_t, "WHEN")
macdef WHERE = $extval (token_t, "WHERE")
macdef WHILE = $extval (token_t, "WHILE")
macdef WHILESTAR = $extval (token_t, "WHILESTAR")
macdef WITH = $extval (token_t, "WITH")
macdef WITHPROP = $extval (token_t, "WITHPROP")
macdef WITHTYPE = $extval (token_t, "WITHTYPE")
macdef WITHVIEW = $extval (token_t, "WITHVIEW")
macdef WITHVIEWTYPE = $extval (token_t, "WITHVIEWTYPE")

// $-keywords
macdef DLRDECRYPT = $extval (token_t, "DLRDECRYPT")
macdef DLRENCRYPT = $extval (token_t, "DLRENCRYPT")
macdef DLRDELAY = $extval (token_t, "DLRDELAY")
macdef DLREXEC = $extval (token_t, "DLREXEC")
macdef DLREXIT = $extval (token_t, "DLREXIT")
macdef DLREXTERN = $extval (token_t, "DLREXTERN")
macdef DLRFOLD = $extval (token_t, "DLRFOLD")
macdef DLRRAISE = $extval (token_t, "DLRRAISE")
macdef DLRUNFOLD = $extval (token_t, "DLRUNFOLD")

// #-keywords
macdef SRPASSERT = $extval (token_t, "SRPASSERT")
macdef SRPDEFINE = $extval (token_t, "SRPDEFINE")
macdef SRPIF = $extval (token_t, "SRPIF")
macdef SRPELSE = $extval (token_t, "SRPELSE")
macdef SRPELIF = $extval (token_t, "SRPELIF")
macdef SRPENDIF = $extval (token_t, "SRPENDIF")
macdef SRPERROR = $extval (token_t, "SRPERROR")
macdef SRPINCLUDE = $extval (token_t, "SRPINCLUDE")
macdef SRPTHEN = $extval (token_t, "SRPTHEN")
macdef SRPWARNING = $extval (token_t, "SRPWARNING")

// keywords-@

macdef FOLDAT = $extval (token_t, "FOLDAT")
macdef FREEAT = $extval (token_t, "FREEAT")
macdef VIEWAT = $extval (token_t, "VIEWAT")

//

macdef LPAREN = $extval (token_t, "LPAREN")
macdef RPAREN = $extval (token_t, "RPAREN")
macdef LBRACKET = $extval (token_t, "LBRACKET")
macdef RBRACKET = $extval (token_t, "RBRACKET")
macdef LBRACE = $extval (token_t, "LBRACE")
macdef RBRACE = $extval (token_t, "RBRACE")
macdef QUOTELPAREN = $extval (token_t, "QUOTELPAREN")
macdef QUOTELBRACKET = $extval (token_t, "QUOTELBRACKET")
macdef QUOTELBRACE = $extval (token_t, "QUOTELBRACE")
macdef ATLPAREN = $extval (token_t, "ATLPAREN")
macdef ATLBRACKET = $extval (token_t, "ATLBRACKET")
macdef ATLBRACE = $extval (token_t, "ATLBRACE")
macdef HASHLPAREN = $extval (token_t, "HASHLPAREN")
macdef HASHLBRACKET = $extval (token_t, "HASHLBRACKET")
macdef HASHLBRACE = $extval (token_t, "HASHLBRACE")

//

macdef AMPERSAND = $extval (token_t, "AMPERSAND")
macdef BACKQUOTE = $extval (token_t, "BACKQUOTE")
macdef BACKSLASH = $extval (token_t, "BACKSLASH")
macdef BANG = $extval (token_t, "BANG")
macdef BAR = $extval (token_t, "BAR")
macdef COMMA = $extval (token_t, "COMMA")
macdef COLON = $extval (token_t, "COLON")
macdef SEMICOLON = $extval (token_t, "SEMICOLON")
macdef DOT = $extval (token_t, "DOT")
macdef EQ = $extval (token_t, "EQ")
macdef LT = $extval (token_t, "LT")
macdef GT = $extval (token_t, "GT")
macdef HASH = $extval (token_t, "HASH")
macdef TILDA = $extval (token_t, "TILDA")
macdef DOTDOT = $extval (token_t, "DOTDOT")
macdef DOTDOTDOT = $extval (token_t, "DOTDOTDOT")
macdef EQLT = $extval (token_t, "EQLT")
macdef EQGT = $extval (token_t, "EQGT")
macdef EQLTGT = $extval (token_t, "EQLTGT")
macdef EQSLASHGT = $extval (token_t, "EQSLASHGT")
macdef EQGTGT = $extval (token_t, "EQGTGT")
macdef EQSLASHGTGT = $extval (token_t, "EQSLASHGTGT")
macdef GTLT = $extval (token_t, "GTLT")
macdef DOTLT = $extval (token_t, "DOTLT")
macdef GTDOT = $extval (token_t, "GTDOT")
macdef DOTLTGTDOT = $extval (token_t, "DOTLTGTDOT")
macdef MINUSLT = $extval (token_t, "MINUSLT")
macdef MINUSGT = $extval (token_t, "MINUSGT")
macdef MINUSLTGT = $extval (token_t, "MINUSLTGT")
macdef COLONLT = $extval (token_t, "COLONLT")
macdef COLONLTGT = $extval (token_t, "COLONLTGT")
macdef BACKQUOTELPAREN = $extval (token_t, "BACKQUOTELPAREN")
macdef COMMALPAREN = $extval (token_t, "COMMALPAREN")
macdef PERCENTLPAREN = $extval (token_t, "PERCENTLPAREN")
macdef BACKQUOTELBRACKET = $extval (token_t, "BACKQUOTELBRACKET")
macdef COMMALBRACKET = $extval (token_t, "COMMALBRACKET")
macdef BACKQUOTELBRACE = $extval (token_t, "BACKQUOTELBRACE")
macdef COMMALBRACE = $extval (token_t, "COMMALBRACE")

(* ****** ****** *)

// implemented in [ats_grammar.yats]
extern fun yylval_char_set (_: $Syn.c0har): void = "yylval_char_set"
extern fun yylval_extcode_set (_: $Syn.e0xtcode): void = "yylval_extcode_set"
extern fun yylval_float_set (_: $Syn.f0loat): void = "yylval_float_set"
extern fun yylval_floatsp_set (_: $Syn.f0loatsp): void = "yylval_floatsp_set"
extern fun yylval_ide_set (_: $Syn.i0de): void = "yylval_ide_set"
extern fun yylval_int_set (_: $Syn.i0nt): void = "yylval_int_set"
extern fun yylval_intsp_set (_: $Syn.i0ntsp): void = "yylval_intsp_set"
extern fun yylval_string_set (_: $Syn.s0tring): void = "yylval_string_set"
extern fun yylval_token_set (_: $Syn.t0kn): void = "yylval_string_set"

(* ****** ****** *)

fn process_token (): void = let
  val fstpos = lexing_fstpos_get ()
  val fstoff = position_toff fstpos
  val lstpos = lexing_lstpos_get ()
  val lstoff = position_toff lstpos
  val loc = begin
    $Loc.location_make ($Fil.the_filename_get (), fstpos, lstpos)
  end // end of [val]
in
  yylval_token_set ($Syn.t0kn_make loc);
end // end of [process_token]

fn process_keyword (): void = let
  val fstpos = lexing_fstpos_get ()
  val fstoff = position_toff fstpos
  val lstpos = lexing_lstpos_get ()
  val lstoff = position_toff lstpos
  val loc = begin
    $Loc.location_make ($Fil.the_filename_get (), fstpos, lstpos)
  end // end of [val]
(*
  val () = begin
    print "process_keyword:\n";
    print "fstpos = "; print fstpos; print_newline ();
    print "lstpos = "; print lstpos; print_newline ();
  end // end of [val]
*)
in
  $POSMARK.posmark_insert_keyword_beg fstoff;
  $POSMARK.posmark_insert_keyword_end lstoff;
  yylval_token_set ($Syn.t0kn_make loc);
end // end of [process_keyword]

(* ****** ****** *)

fn process_comment_open (
  p: position_t, ps: poslst
) : void =
//
let val fstpos = lexing_fstpos_get () in
  COMMENT (fstpos, POSLSTcons (p, ps))
end
//
fn process_comment_close
  (p0: position_t, ps: poslst): void = begin
  case+ ps of
  | ~POSLSTcons (p, ps) => COMMENT (p, ps)
  | ~POSLSTnil () => let
      val lstpos = lexing_lstpos_get ()
      val lstoff = position_toff lstpos
    in
      $POSMARK.posmark_insert_comment_end lstoff
    end // end of [POSLSTnil]
// end of [process_comment_close]
//
end // end of [process_comment_close]

(* ****** ****** *)

fn process_comment_clike_open
  (p1: position_t): void = let
  val p2 = lexing_fstpos_get ()
in
  prerr_string "The comment starting at [";
  prerr_position p2;
  prerr_string "] cannot be embedded in another C-like comment";
  prerr_string ", which initiates from [";
  prerr_position p1;
  prerr_string "].";
  prerr_newline ();
  $raise LexingErrorException
end // end of [process_comment_clike_open]

fn process_comment_clike_close
  (fstpos: position_t): void = let
  val lstpos = lexing_lstpos_get ()
  val lstoff = position_toff lstpos
in
  $POSMARK.posmark_insert_comment_end lstoff
end // end of [process_comment_clike_close]

(* ****** ****** *)

fn process_comment_line_open (): void = let
  val fstpos = lexing_fstpos_get ()
  val fstoff = position_toff fstpos
in
  $POSMARK.posmark_insert_comment_beg fstoff
end // end of [process_comment_line_open]

fn process_comment_line_close (): void = let
  val lstpos = lexing_lstpos_get ()
  val lstoff = position_toff lstpos
in
  $POSMARK.posmark_insert_comment_end lstoff
end // end of [process_comment_line_close]

(* ****** ****** *)

fn process_comment_rest_open (): void = let
  val fstpos = lexing_fstpos_get ()
  val fstoff = position_toff fstpos
in
  $POSMARK.posmark_insert_comment_beg fstoff
end // end of [process_comment_rest_open]

fn process_comment_rest_close (): void = let
  val lstpos = lexing_lstpos_get ()
  val lstoff = position_toff lstpos
in
  $POSMARK.posmark_insert_comment_end lstoff
end // end of [process_comment_rest_close]

(* ****** ****** *)

fn location_get (): $Loc.location_t = $Loc.location_make
  ($Fil.the_filename_get (), lexing_fstpos_get (), lexing_lstpos_get ())
// end of [location_get]

fn location_get_pos (fstpos: position_t): $Loc.location_t =
  $Loc.location_make ($Fil.the_filename_get (), fstpos, lexing_lstpos_get ())
// end of [location_get_pos]

fn tokenize_identifier_alp (): token_t = let
  val str = lexeme_string ()
(*
  val () = begin
    print "tokenize_identifier_alp: str = "; print str; print_newline ()
  end // end of [val]
*)
  val tok = keyword_search str
in
  if token_is_valid tok then let
    val () = process_keyword () in tok
  end else let // not a keyword
    val loc = location_get ()
  in
    yylval_ide_set ($Syn.i0de_make (loc, str)); IDENTIFIER_alp
  end // end of [if]
end // end of [tokenize_identifier_alp]

fn tokenize_identifier_sym (): token_t = let
  val str = lexeme_string ()
(*
  val () = begin
    print "tokenize_identifier_sym: str = "; print str; print_newline ()
  end // end of [val]
*)
  val tok = keyword_search str
in
  if token_is_valid tok then let
    val () = process_keyword () in tok
  end else let // not a keyword
    val loc = location_get ()
  in
    yylval_ide_set ($Syn.i0de_make (loc, str)); IDENTIFIER_sym
  end // end of [if]
end // end of [tokenize_identifier_sym]

(* ****** ****** *)

fn prefix_identifier1 (s0: string): string = let
  val s0 = string1_of_string s0; val n0 = string_length s0
in
  if n0 > 0 then let
    val sbp = string_make_substring (s0, 0, n0-1) in string1_of_strbuf sbp
  end else s0
end // end of [prefix_identifier1]

(* ****** ****** *)
   
fn tokenize_identifier_arr
  (): token_t = let // array identifier
  val str = prefix_identifier1 (lexeme_string ())
  val loc = location_get ()
in
  yylval_ide_set ($Syn.i0de_make (loc, str)); IDENTIFIER_arr
end // end of [tokenize_identifier_arr]

fn tokenize_identifier_tmp
  (): token_t = let // template identifier
  val str = prefix_identifier1 (lexeme_string ())
  val loc = location_get ()
in
  yylval_ide_set ($Syn.i0de_make (loc, str)); IDENTIFIER_tmp
end // end of [tokenize_identifier_tmp]

fn tokenize_identifier_ext
  (): token_t = let // template identifier
  val str = prefix_identifier1 (lexeme_string ())
  val loc = location_get ()
in
  yylval_ide_set ($Syn.i0de_make (loc, str)); IDENTIFIER_ext
end // end of [tokenize_identifier_ext]

(* ****** ****** *)

fn tokenize_identifier_dlr (): token_t = let // $-identifier
  val str = lexeme_string ()
  val tok = keyword_search str
in
  if token_is_valid tok then (process_keyword (); tok)
  else let
    val loc = location_get ()
  in
    yylval_ide_set ($Syn.i0de_make (loc, str)); IDENTIFIER_dlr
  end
end // end of [tokenize_identifier_dlr]

fn tokenize_identifier_srp (): token_t = let // #-identifier
  val str = lexeme_string ()
  val tok = keyword_search str
in
  if token_is_valid tok then (process_keyword (); tok)
  else let
    val loc = location_get ()
  in
    yylval_ide_set ($Syn.i0de_make (loc, str)); IDENTIFIER_srp
  end
end // end of [tokenize_identifier_srp]

(* ****** ****** *)

fn process_char (fstpos: position_t): void = let
  val chr = lexeme_get 0; val loc = location_get_pos (fstpos)
in
  yylval_char_set ($Syn.c0har_make (loc, chr))
end // end of [process_char]

fn char_for_escaped (c: char): char = begin
  case+ c of
    | 'a' => '\007' (* alert *)
    | 'b' => '\010' (* backspace *)
    | 'f' => '\014' (* line feed *)
    | 't' => '\011' (* horizontal tab *)
    | 'n' => '\012' (* newline *)
    | 'r' => '\015' (* carriage return *)
    | 'v' => '\013' (* vertical tab *)
    |  _  => c
end // end of [char_for_escaped]

fn process_char_escaped
  (fstpos: position_t): void = let
  val chr = char_for_escaped (lexeme_get 1)
  val loc = location_get_pos (fstpos)
in
  yylval_char_set ($Syn.c0har_make (loc, chr))
end // end of [process_char_escaped]

fn char_for_oct_code_1 (i: int): char =
  char_of_int (lexeme_get i - '0')

fn process_char_oct_1
  (fstpos: position_t): void = let
  val chr = char_for_oct_code_1 (1)
  val loc = location_get_pos (fstpos)
in
  yylval_char_set ($Syn.c0har_make (loc, chr))
end // end of [process_char_oct_1]

fn char_for_oct_code_2 (i: int): char = let
  val (pf_lxbf | ptr_lxbf) = lexing_lexbuf_get ()
  val d0 = lexeme_get_lexbuf (!ptr_lxbf, i) - '0'
  val d1 = lexeme_get_lexbuf (!ptr_lxbf, i+1) - '0'
  val () = lexing_lexbuf_set (pf_lxbf | ptr_lxbf)
in
  char_of_int ((d0 << 3) + d1)
end // end of [char_for_oct_code_2]

fn process_char_oct_2
  (fstpos: position_t): void = let
  val chr = char_for_oct_code_2 (1)
  val loc = location_get_pos (fstpos)
in
  yylval_char_set ($Syn.c0har_make (loc, chr))
end // end of [process_char_oct_2]

fn char_for_oct_code_3 (i: int): char = let
  val (pf_lxbf | ptr_lxbf) = lexing_lexbuf_get ()
  val d0 = lexeme_get_lexbuf (!ptr_lxbf, i) - '0'
  val d1 = lexeme_get_lexbuf (!ptr_lxbf, i+1) - '0'
  val d2 = lexeme_get_lexbuf (!ptr_lxbf, i+2) - '0'
  val () = lexing_lexbuf_set (pf_lxbf | ptr_lxbf)
in
  char_of_int ((d0 << 6) + (d1 << 3) + d2)
end // end of [char_for_oct_code_3]

fn process_char_oct_3
  (fstpos: position_t): void = let
  val chr = char_for_oct_code_3 (1)
  val loc = location_get_pos (fstpos)
in
  yylval_char_set ($Syn.c0har_make (loc, chr))
end // end of [char_for_oct_code_3]

(* ****** ****** *)

fn int_of_xdigit (c: char): int =
  if char_isdigit c then c - '0' else begin
    if char_isupper c then 10 + (c - 'A') else 10 + (c - 'a')
  end (* end of [if] *)
(* end of [int_of_xdigit] *)    

fn char_for_hex_code_1 (i: int): char = let
  val d0 = int_of_xdigit (lexeme_get i) in char_of_int d0
end // end of [char_for_hex_code_1]

fn process_char_hex_1
  (fstpos: position_t): void = let
  val chr = char_for_hex_code_1 (2)
  val loc = location_get_pos (fstpos)
in
  yylval_char_set ($Syn.c0har_make (loc, chr))
end // end of [process_char_hex_1]

fn char_for_hex_code_2 (i: int): char = let
  val (pf_lxbf | ptr_lxbf) = lexing_lexbuf_get ()
  val d0 = int_of_xdigit (lexeme_get_lexbuf (!ptr_lxbf, i))
  val d1 = int_of_xdigit (lexeme_get_lexbuf (!ptr_lxbf, i+1))
  val () = lexing_lexbuf_set (pf_lxbf | ptr_lxbf)
in
  char_of_int ((d0 << 4) + d1)
end // end of [char_for_hex_code_2]

fn process_char_hex_2
  (fstpos: position_t): void = let
  val chr = char_for_hex_code_2 (2)
  val loc = location_get_pos (fstpos)
in
  yylval_char_set ($Syn.c0har_make (loc, chr))
end // end of [process_char_hex_2]

(* ****** ****** *)

fn process_literal_float (): void = let
  val loc = location_get (); val str = lexeme_string ()
in
  yylval_float_set ($Syn.f0loat_make (loc, str))
end // end of [process_literal_float]

fn process_literal_floatsp (): void = let
  val str = lexeme_string (); val loc = location_get ()
in
  yylval_floatsp_set ($Syn.f0loatsp_make (loc, str))
end // end of [process_literal_floatsp]

(* ****** ****** *)

%{$

ats_bool_type
ats_lexer_literal_int_check // HX: checking octal numbers
  (ats_ptr_type s0, ats_ptr_type err) {
  char c, *s = s0 ;
//
  c = *s ;
  if (c != '0') return ats_true_bool ;
  ++s ; c = *s ;
  while (1) {
    if (isdigit (c)) {
      if (c >= '8') { *((char*)err) = c; return ats_false_bool ; }
    } else {
      return ats_true_bool ;
    } // end of [if]
    ++s ; c = *s ;
  } // end of [while]
//
  return ats_true_bool ;
} /* end of [ats_lexer_literal_int_check] */

%} // end of [...]

extern
fun process_literal_int_check // HX: checking octal numbers
  (_: string, err: &char): bool = "ats_lexer_literal_int_check"
// end of [process_literal_int_check]

fn process_literal_int (): void = let
  val str = lexeme_string ()
(*
  val () = printf ("process_literal_int: str = %s\n", @(str))
*)
  val loc = location_get ()
  var err: char = '\000'; val () =
    if process_literal_int_check (str, err) then () else begin
      prerr loc;
      prerr ": the digit ["; prerr err;
      prerr "] is illegal in the octal constant [";
      prerr str; prerr "].";
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [if]
in
  yylval_int_set ($Syn.i0nt_make (loc, str))
end // end of [process_literal_int]

extern
fun process_literal_intsp_check // HX: checking octal numbers
  (_: string, err: &char): bool = "ats_lexer_literal_int_check"
// end of [process_literal_intsp_check]

fn process_literal_intsp (): void = let
  val str = lexeme_string (); val loc = location_get ()
  var err: char = '\000'; val () =
    if process_literal_intsp_check (str, err) then () else begin
      prerr loc;
      prerr ": the digit ["; prerr err;
      prerr "] is illegal in the octal constant [";
      prerr str; prerr "].";
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [if]
in
  yylval_intsp_set ($Syn.i0ntsp_make (loc, str))
end // end of [process_literal_intsp]

(* ****** ****** *)

fn STRING_char {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): token_t =
  let val c = lexeme_get 0 in
    STRING (fstpos, $CS.CHARLSTcons (c, cs), n+1)
  end

fn STRING_char_escaped {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): token_t =
  let val c = char_for_escaped (lexeme_get 1) in
    STRING (fstpos, $CS.CHARLSTcons (c, cs), n+1)
  end

fn STRING_char_oct_1 {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): token_t =
  let val c = char_for_oct_code_1 (1) in
    STRING (fstpos, $CS.CHARLSTcons (c, cs), n+1)
  end

fn STRING_char_oct_2 {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): token_t =
  let val c = char_for_oct_code_2 (1) in
    STRING (fstpos, $CS.CHARLSTcons (c, cs), n+1)
  end

fn STRING_char_oct_3 {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): token_t =
  let val c = char_for_oct_code_3 (1) in
    STRING (fstpos, $CS.CHARLSTcons (c, cs), n+1)
  end

fn STRING_char_hex_1 {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): token_t =
  let val c = char_for_hex_code_1 (2) in
    STRING (fstpos, $CS.CHARLSTcons (c, cs), n+1)
  end

fn STRING_char_hex_2 {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): token_t =
  let val c = char_for_hex_code_2 (2) in
    STRING (fstpos, $CS.CHARLSTcons (c, cs), n+1)
  end

fn process_literal_string {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): void = let
  val str = $CS.string_make_charlst_rev_int (cs, n)
  val loc = location_get_pos (fstpos)
in
  yylval_string_set ($Syn.s0tring_make (loc, str, n))
end // end of [process_literal_string]

(* ****** ****** *)

fn EXTCODE_char {n:nat}
  (fstpos: position_t, i: int, cs: $CS.charlst_vt n, n: int n): token_t =
  let val c = lexeme_get 0 in
    EXTCODE (fstpos, i, $CS.CHARLSTcons (c, cs), n+1)
  end

fn process_literal_extcode {n:nat}
  (fstpos: position_t, i: int, cs: $CS.charlst_vt n, n: int n): void =
  let
    val str = $CS.string_make_charlst_rev_int (cs, n)
    val loc = location_get_pos (fstpos)
  in
    yylval_extcode_set ($Syn.e0xtcode_make (loc, i, str))
  end

(* ****** ****** *)

(*

// declared in [lexing.sats]
exception LexingErrorException

*)

fn process_illegal_token {a:viewt@ype} (): a = begin
  $Fil.atsopt_filename_prerr ();
  prerr_string ": LEXING ERROR";
  prerr_string ": illegal character [";
  prerr_char (lexeme_get 0);
  prerr_string "] at position [";
  lexing_curpos_prerr ();
  prerr_string "].";
  prerr_newline ();
  $raise LexingErrorException
end // end of [process_illegal_token]

fn process_illegal_char
  {a:viewt@ype} (fstpos: position_t): a = begin
  $Fil.atsopt_filename_prerr ();
  prerr_string ": LEXING ERROR";
  prerr_string ": illegal character at [";
  prerr_position fstpos;
  prerr_string "] is unclosed!\n";
  $raise LexingErrorException
end // end of [process_illegal_char]

//

fn process_unclosed_comment
  {a:viewt@ype} (p: position_t, ps: poslst): a = let
  val () = poslst_free ps
in
  prerr_string "The comment starting at [";
  prerr_position p;
  prerr_string "] is unclosed!\n";
  $raise LexingErrorException
end // end of [process_unclosed_comment]

fn process_unclosed_comment_clike
  {a:viewt@ype} (p: position_t): a = begin
  prerr_string "The comment starting at [";
  prerr_position p;
  prerr_string "] is unclosed!\n";
  $raise LexingErrorException
end // end of [process_unclosed_comment_clike]

//

fn process_unclosed_string {a:viewt@ype} {n:nat}
  (fstpos: position_t, cs: $CS.charlst_vt n, n: int n): a = begin
  $CS.charlst_free (cs);
  prerr_string "The string starting at [";
  prerr_position fstpos;
  prerr_string "] is unclosed!\n";
  $raise LexingErrorException
end // end of [process_unclosed_string]

fn process_unclosed_extcode {a:viewt@ype} {n:nat}
  (fstpos: position_t, i: int, cs: $CS.charlst_vt n, n: int n)
  : a = begin
  $CS.charlst_free (cs);
  prerr_string "The code starting at [";
  prerr_position fstpos;
  prerr_string "] is unclosed!\n";
  $raise LexingErrorException
end // end of [process_unclosed_extcode]

(* ****** ****** *)

(* end of preamble *)

val __MAIN_transition_table: transition_table_t = __transition_table_make 172 "\
\000\044\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\043\000\043\000\002\000\043\000\043\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\043\000\025\000\042\000\041\000\040\000\037\000\005\000\036\000\035\000\034\000\005\000\005\000\033\000\005\000\005\000\032\000\031\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\005\000\027\000\026\000\005\000\026\000\025\000\024\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\023\000\022\000\021\000\005\000\007\000\020\000\017\000\007\000\016\000\007\000\007\000\015\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\014\000\007\000\013\000\007\000\012\000\007\000\011\000\010\000\007\000\007\000\007\000\006\000\005\000\004\000\003\000\002\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\000\000\000\000\053\000\053\000\000\000\053\000\053\000\053\000\254\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\000\000\000\000\053\000\053\000\000\000\053\000\053\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\247\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\222\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\221\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\207\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\206\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\202\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\175\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\163\000\162\000\130\000\130\000\161\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\154\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\131\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\127\000\000\000\053\000\053\000\000\000\053\000\053\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\117\000\000\000\053\000\053\000\000\000\053\000\053\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\116\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\115\000\000\000\000\000\000\000\000\000\000\000\114\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\113\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\046\000\046\000\000\000\000\000\000\000\046\000\046\000\000\000\046\000\046\000\046\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\000\000\046\000\000\000\046\000\046\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\055\000\055\000\000\000\000\000\000\000\055\000\055\000\000\000\055\000\055\000\055\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\055\000\055\000\055\000\000\000\055\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\055\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\055\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\077\000\000\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\077\000\000\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\073\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\073\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\000\000\000\000\070\000\053\000\000\000\053\000\053\000\067\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\066\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\065\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\064\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\063\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\062\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\056\000\000\000\053\000\053\000\000\000\053\000\053\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\054\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\046\000\046\000\000\000\000\000\000\000\046\000\046\000\000\000\046\000\046\000\046\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\000\000\046\000\000\000\046\000\046\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\000\000\000\000\000\000\046\000\052\000\046\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\000\000\046\000\000\000\046\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\046\000\046\000\000\000\000\000\000\000\046\000\046\000\000\000\046\000\046\000\046\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\000\000\046\000\000\000\046\000\046\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\051\000\000\000\000\000\046\000\050\000\046\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\047\000\046\000\000\000\046\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\045\000\045\000\000\000\045\000\045\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\045\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\045\000\045\000\000\000\045\000\045\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\045\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\046\000\046\000\000\000\000\000\000\000\046\000\046\000\000\000\046\000\046\000\046\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\000\000\046\000\000\000\046\000\046\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\050\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\000\000\000\000\000\000\000\000\050\000\000\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\052\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\000\000\000\000\000\000\000\000\052\000\000\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\000\000\000\000\053\000\053\000\000\000\053\000\053\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\061\000\060\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\057\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\055\000\055\000\000\000\000\000\000\000\055\000\055\000\000\000\055\000\055\000\055\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\055\000\055\000\055\000\000\000\055\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\055\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\055\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\000\000\000\000\053\000\053\000\000\000\053\000\053\000\071\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\000\000\000\000\053\000\053\000\000\000\053\000\053\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\000\000\000\000\053\000\053\000\000\000\053\000\053\000\072\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\046\000\053\000\053\000\000\000\000\000\000\000\053\000\053\000\000\000\053\000\053\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\055\000\053\000\055\000\046\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\000\000\053\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\112\000\112\000\112\000\112\000\112\000\112\000\112\000\112\000\112\000\112\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\112\000\112\000\112\000\112\000\112\000\112\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\112\000\112\000\112\000\112\000\112\000\112\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\111\000\000\000\111\000\000\000\000\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\077\000\000\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\102\000\102\000\102\000\102\000\102\000\102\000\102\000\102\000\102\000\102\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\101\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\101\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\107\000\000\000\107\000\000\000\000\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\102\000\102\000\102\000\102\000\102\000\102\000\102\000\102\000\102\000\102\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\103\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\103\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\105\000\000\000\105\000\000\000\000\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\100\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\110\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\112\000\112\000\112\000\112\000\112\000\112\000\112\000\112\000\112\000\112\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\112\000\112\000\112\000\112\000\112\000\112\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\112\000\112\000\112\000\112\000\112\000\112\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\123\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\122\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\120\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\121\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\125\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\124\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\126\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\135\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\137\000\130\000\136\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\144\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\140\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\141\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\142\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\143\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\145\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\146\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\147\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\150\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\151\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\152\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\153\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\155\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\156\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\160\000\000\000\157\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\172\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\166\000\130\000\130\000\130\000\130\000\130\000\165\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\164\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\171\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\167\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\170\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\173\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\174\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\176\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\177\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\201\000\000\000\200\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\203\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\204\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\205\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\215\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\211\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\212\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\214\000\000\000\213\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\216\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\220\000\000\000\217\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\226\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\223\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\225\000\000\000\224\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\227\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\233\000\000\000\232\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\231\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\230\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\235\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\234\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\243\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\236\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\237\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\240\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\242\000\000\000\241\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\244\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\246\000\000\000\245\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\250\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\251\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\252\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\253\000\000\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\133\000\000\000\000\000\000\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\132\000\000\000\000\000\000\000\130\000\000\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\130\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\077\000\000\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\076\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\073\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\073\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __MAIN_accept_table: accept_table_t = __accept_table_make 172 143 "\
\000\002\000\113\
\000\044\000\112\
\000\060\000\110\
\000\061\000\111\
\000\057\000\106\
\000\056\000\103\
\000\066\000\102\
\000\042\000\104\
\000\022\000\100\
\000\127\000\101\
\000\033\000\076\
\000\051\000\074\
\000\113\000\072\
\000\047\000\073\
\000\116\000\071\
\000\027\000\077\
\000\054\000\107\
\000\063\000\066\
\000\064\000\065\
\000\062\000\067\
\000\004\000\064\
\000\006\000\063\
\000\034\000\060\
\000\023\000\061\
\000\021\000\062\
\000\036\000\105\
\000\117\000\070\
\000\106\000\055\
\000\104\000\055\
\000\102\000\055\
\000\077\000\055\
\000\112\000\053\
\000\030\000\053\
\000\074\000\054\
\000\031\000\053\
\000\026\000\052\
\000\254\000\053\
\000\025\000\052\
\000\046\000\052\
\000\005\000\052\
\000\055\000\052\
\000\020\000\052\
\000\050\000\051\
\000\041\000\052\
\000\053\000\052\
\000\003\000\052\
\000\037\000\052\
\000\134\000\047\
\000\040\000\052\
\000\052\000\050\
\000\132\000\045\
\000\007\000\044\
\000\065\000\043\
\000\035\000\057\
\000\071\000\052\
\000\072\000\040\
\000\153\000\037\
\000\032\000\052\
\000\067\000\041\
\000\070\000\042\
\000\130\000\044\
\000\133\000\046\
\000\145\000\044\
\000\144\000\044\
\000\136\000\044\
\000\146\000\044\
\000\147\000\044\
\000\076\000\053\
\000\110\000\055\
\000\135\000\044\
\000\131\000\044\
\000\241\000\035\
\000\242\000\034\
\000\017\000\044\
\000\137\000\044\
\000\214\000\031\
\000\212\000\030\
\000\213\000\032\
\000\205\000\027\
\000\240\000\033\
\000\143\000\036\
\000\013\000\044\
\000\121\000\026\
\000\124\000\024\
\000\174\000\022\
\000\231\000\023\
\000\024\000\052\
\000\170\000\021\
\000\161\000\044\
\000\172\000\044\
\000\173\000\044\
\000\253\000\020\
\000\166\000\044\
\000\167\000\044\
\000\252\000\044\
\000\126\000\025\
\000\250\000\044\
\000\010\000\044\
\000\245\000\016\
\000\243\000\044\
\000\234\000\044\
\000\244\000\044\
\000\246\000\017\
\000\247\000\044\
\000\251\000\044\
\000\100\000\056\
\000\227\000\044\
\000\225\000\013\
\000\221\000\044\
\000\226\000\044\
\000\232\000\014\
\000\222\000\044\
\000\223\000\044\
\000\220\000\011\
\000\011\000\044\
\000\224\000\012\
\000\233\000\015\
\000\216\000\044\
\000\217\000\010\
\000\012\000\044\
\000\206\000\044\
\000\200\000\006\
\000\201\000\007\
\000\175\000\044\
\000\176\000\044\
\000\165\000\044\
\000\171\000\005\
\000\014\000\044\
\000\177\000\044\
\000\164\000\004\
\000\162\000\044\
\000\160\000\003\
\000\156\000\044\
\000\157\000\002\
\000\154\000\044\
\000\155\000\044\
\000\015\000\044\
\000\016\000\044\
\000\163\000\044\
\000\045\000\001\
\000\043\000\001\
\000\215\000\044\
\000\230\000\044\
"

implement MAIN () =
case+ lexing_engine (__MAIN_transition_table, __MAIN_accept_table) of
  | 1 => (  MAIN ()  )
  | 2 => (  process_keyword (); CASEMINUS  )
  | 3 => (  process_keyword (); CASEPLUS  )
  | 4 => (  process_keyword (); FNSTAR  )
  | 5 => (  process_keyword (); FORSTAR  )
  | 6 => (  process_token (); PROPMINUS  )
  | 7 => (  process_token (); PROPPLUS  )
  | 8 => (  process_token (); TYPEMINUS  )
  | 9 => (  process_token (); TYPEPLUS  )
  | 10 => (  process_keyword (); VALMINUS  )
  | 11 => (  process_keyword (); VALPLUS  )
  | 12 => (  process_token (); VIEWMINUS  )
  | 13 => (  process_token (); VIEWPLUS  )
  | 14 => (  process_token (); VIEWTYPEMINUS  )
  | 15 => (  process_token (); VIEWTYPEPLUS  )
  | 16 => (  process_keyword (); WHILESTAR  )
  | 17 => (  process_token (); FOLDAT  )
  | 18 => (  process_token (); FREEAT  )
  | 19 => (  process_token (); VIEWAT  )
  | 20 => (  process_token (); ATLAM  )
  | 21 => (  process_token (); ATLLAM  )
  | 22 => (  process_token (); ATFIX  )
  | 23 => (  process_token (); R0EAD  )
  | 24 => (  process_token (); T0YPE  )
  | 25 => (  process_token (); T0YPEPLUS  )
  | 26 => (  process_token (); T0YPEMINUS  )
  | 27 => (  process_token (); VIEWT0YPE  )
  | 28 => (  process_token (); VIEWT0YPEPLUS  )
  | 29 => (  process_token (); VIEWT0YPEMINUS  )
  | 30 => (  process_keyword (); ABST0YPE  )
  | 31 => (  process_keyword (); ABSVIEWT0YPE  )
  | 32 => (  process_comment_rest_open (); COMMENT_REST (); TOKEN_eof  )
  | 33 => (  process_comment_line_open (); COMMENT_LINE (); MAIN ()  )
  | 34 => (  COMMENT0_CLIKE (); MAIN ()  )
  | 35 => (  COMMENT0 (); MAIN ()  )
  | 36 => (  tokenize_identifier_alp ()  )
  | 37 => (  tokenize_identifier_arr ()  )
  | 38 => (  tokenize_identifier_tmp ()  )
  | 39 => (  tokenize_identifier_ext ()  )
  | 40 => (  tokenize_identifier_dlr ()  )
  | 41 => (  tokenize_identifier_srp ()  )
  | 42 => (  tokenize_identifier_sym ()  )
  | 43 => (  process_literal_int (); LITERAL_int  )
  | 44 => (  process_literal_intsp (); LITERAL_intsp  )
  | 45 => (  process_literal_float (); LITERAL_float  )
  | 46 => (  process_literal_floatsp (); LITERAL_floatsp  )
  | 47 => (  process_keyword (); LPAREN  )
  | 48 => (  process_keyword (); RPAREN  )
  | 49 => (  process_keyword (); LBRACKET  )
  | 50 => (  process_keyword (); RBRACKET  )
  | 51 => (  process_keyword (); LBRACE  )
  | 52 => (  process_keyword (); RBRACE  )
  | 53 => (  process_keyword (); QUOTELPAREN  )
  | 54 => (  process_keyword (); QUOTELBRACKET  )
  | 55 => (  process_keyword (); QUOTELBRACE  )
  | 56 => (  process_keyword (); ATLPAREN  )
  | 57 => (  process_keyword (); ATLBRACKET  )
  | 58 => (  process_keyword (); ATLBRACE  )
  | 59 => (  process_keyword (); HASHLPAREN  )
  | 60 => (  process_keyword (); HASHLBRACKET  )
  | 61 => (  process_keyword (); HASHLBRACE  )
  | 62 => (  process_keyword (); COMMA  )
  | 63 => (  process_keyword (); SEMICOLON  )
  | 64 => (  process_keyword (); BACKSLASH  )
  | 65 => (  process_keyword (); BACKQUOTELPAREN  )
  | 66 => (  process_keyword (); COMMALPAREN  )
  | 67 => (  process_keyword (); PERCENTLPAREN  )
  | 68 => (  STRING0 ()  )
  | 69 => (  CHAR0 ()  )
  | 70 => (  EXTCODE0 (0)  )
  | 71 => (  EXTCODE0 (1)  )
  | 72 => (  EXTCODE0 (2)  )
  | 73 => (  EXTCODE0 (~1)  )
  | 74 => (  TOKEN_eof  )
  | 75 => (  process_illegal_token ()  )
  | _ => MAIN_lexing_error ()

val __COMMENT_transition_table: transition_table_t = __transition_table_make 7 "\
\000\005\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\004\000\002\000\003\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\
\000\000\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\000\000\002\000\000\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __COMMENT_accept_table: accept_table_t = __accept_table_make 7 7 "\
\000\005\000\006\
\000\003\000\005\
\000\006\000\001\
\000\007\000\002\
\000\004\000\004\
\000\002\000\003\
\000\001\000\003\
"

implement COMMENT (p, ps) =
case+ lexing_engine (__COMMENT_transition_table, __COMMENT_accept_table) of
  | 1 => (  process_comment_open (p, ps)  )
  | 2 => (  process_comment_close (p, ps)  )
  | 3 => (  COMMENT (p, ps)  )
  | 4 => (  COMMENT (p, ps)  )
  | 5 => (  COMMENT (p, ps)  )
  | 6 => (  process_unclosed_comment (p, ps)  )
  | _ => COMMENT_lexing_error (p, ps)

val __COMMENT_CLIKE_transition_table: transition_table_t = __transition_table_make 7 "\
\000\005\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\004\000\002\000\002\000\002\000\002\000\003\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\
\000\000\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\000\000\002\000\002\000\002\000\002\000\000\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __COMMENT_CLIKE_accept_table: accept_table_t = __accept_table_make 7 7 "\
\000\005\000\006\
\000\006\000\002\
\000\004\000\005\
\000\003\000\004\
\000\001\000\003\
\000\007\000\001\
\000\002\000\003\
"

implement COMMENT_CLIKE (p) =
case+ lexing_engine (__COMMENT_CLIKE_transition_table, __COMMENT_CLIKE_accept_table) of
  | 1 => (  process_comment_clike_open (p)  )
  | 2 => (  process_comment_clike_close (p)  )
  | 3 => (  COMMENT_CLIKE (p)  )
  | 4 => (  COMMENT_CLIKE (p)  )
  | 5 => (  COMMENT_CLIKE (p)  )
  | 6 => (  process_unclosed_comment_clike (p)  )
  | _ => COMMENT_CLIKE_lexing_error (p)

val __COMMENT_LINE_transition_table: transition_table_t = __transition_table_make 3 "\
\000\003\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\002\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __COMMENT_LINE_accept_table: accept_table_t = __accept_table_make 3 2 "\
\000\003\000\002\
\000\002\000\001\
"

implement COMMENT_LINE () =
case+ lexing_engine (__COMMENT_LINE_transition_table, __COMMENT_LINE_accept_table) of
  | 1 => (  process_comment_line_close ()  )
  | 2 => (  process_comment_line_close ()  )
  | _ => COMMENT_LINE_lexing_error ()

val __COMMENT_REST_transition_table: transition_table_t = __transition_table_make 3 "\
\000\003\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\002\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __COMMENT_REST_accept_table: accept_table_t = __accept_table_make 3 2 "\
\000\003\000\002\
\000\002\000\001\
"

implement COMMENT_REST () =
case+ lexing_engine (__COMMENT_REST_transition_table, __COMMENT_REST_accept_table) of
  | 1 => (  COMMENT_REST ()  )
  | 2 => (  process_comment_rest_close ()  )
  | _ => COMMENT_REST_lexing_error ()

val __CHAR_transition_table: transition_table_t = __transition_table_make 17 "\
\000\000\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\003\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\004\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\000\000\004\000\004\000\000\000\000\000\000\000\000\000\004\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\004\000\000\000\004\000\000\000\005\000\000\000\000\000\004\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\014\000\014\000\014\000\014\000\014\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\014\000\014\000\014\000\014\000\014\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\010\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\012\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\015\000\015\000\015\000\015\000\015\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\015\000\015\000\015\000\015\000\015\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __CHAR_accept_table: accept_table_t = __accept_table_make 17 9 "\
\000\016\000\007\
\000\017\000\006\
\000\010\000\005\
\000\020\000\002\
\000\013\000\003\
\000\003\000\010\
\000\012\000\004\
\000\021\000\001\
\000\002\000\010\
"

implement CHAR (pos) =
case+ lexing_engine (__CHAR_transition_table, __CHAR_accept_table) of
  | 1 => (  process_char (pos); LITERAL_char  )
  | 2 => (  process_char_escaped (pos); LITERAL_char  )
  | 3 => (  process_char_oct_3 (pos); LITERAL_char  )
  | 4 => (  process_char_oct_2 (pos); LITERAL_char  )
  | 5 => (  process_char_oct_1 (pos); LITERAL_char  )
  | 6 => (  process_char_hex_2 (pos); LITERAL_char  )
  | 7 => (  process_char_hex_1 (pos); LITERAL_char  )
  | 8 => (  process_illegal_char (pos)  )
  | _ => CHAR_lexing_error (pos)

val __STRING_transition_table: transition_table_t = __transition_table_make 13 "\
\000\005\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\004\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\003\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\011\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\006\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000\000\000\000\000\006\000\006\000\000\000\000\000\000\000\000\000\006\000\006\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\006\000\000\000\006\000\000\000\006\000\000\000\007\000\000\000\000\000\006\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\014\000\014\000\014\000\014\000\014\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\014\000\014\000\014\000\014\000\014\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\012\000\012\000\012\000\012\000\012\000\012\000\012\000\012\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\015\000\015\000\015\000\015\000\015\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\015\000\015\000\015\000\015\000\015\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __STRING_accept_table: accept_table_t = __accept_table_make 13 11 "\
\000\002\000\012\
\000\005\000\011\
\000\014\000\010\
\000\015\000\007\
\000\010\000\006\
\000\006\000\003\
\000\011\000\002\
\000\012\000\005\
\000\013\000\004\
\000\004\000\001\
\000\003\000\012\
"

implement STRING (pos, cs, n) =
case+ lexing_engine (__STRING_transition_table, __STRING_accept_table) of
  | 1 => (  process_literal_string (pos, cs, n); LITERAL_string  )
  | 2 => (  STRING (pos, cs, n)  )
  | 3 => (  STRING_char_escaped (pos, cs, n)  )
  | 4 => (  STRING_char_oct_3 (pos, cs, n)  )
  | 5 => (  STRING_char_oct_2 (pos, cs, n)  )
  | 6 => (  STRING_char_oct_1 (pos, cs, n)  )
  | 7 => (  STRING_char_hex_2 (pos, cs, n)  )
  | 8 => (  STRING_char_hex_1 (pos, cs, n)  )
  | 9 => (  process_unclosed_string (pos, cs, n)  )
  | 10 => (  STRING_char (pos, cs, n)  )
  | _ => STRING_lexing_error (pos, cs, n)

val __EXTCODE_transition_table: transition_table_t = __transition_table_make 5 "\
\000\004\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\003\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __EXTCODE_accept_table: accept_table_t = __accept_table_make 5 4 "\
\000\005\000\001\
\000\004\000\002\
\000\003\000\003\
\000\002\000\003\
"

implement EXTCODE (pos, i, cs, n) =
case+ lexing_engine (__EXTCODE_transition_table, __EXTCODE_accept_table) of
  | 1 => (  process_literal_extcode (pos, i, cs, n); LITERAL_extcode  )
  | 2 => (  process_unclosed_extcode (pos, i, cs, n)  )
  | 3 => (  EXTCODE_char (pos, i, cs, n)  )
  | _ => EXTCODE_lexing_error (pos, i, cs, n)



%{

ats_void_type ats_lexer_lats_initialize () {
  // currently empty
  return ;
}

//

ats_bool_type token_is_valid (ats_int_type tok) {
  return (tok >= 0 ? ats_true_bool : ats_false_bool) ;
}

%} // end of [%{]

(* ****** ****** *)

(* end of [ats_lexer.lats] *)
