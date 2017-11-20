 // preamble

(* ****** ****** *)

staload "libats_lex_lexing.sats"

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_string_parse.sats"

(* ****** ****** *)

fun printf_c_argtypes_free (ts: printf_c_argtypes): void = case+ ts of
  | ~list_vt_cons (_, ts) => printf_c_argtypes_free ts | ~list_vt_nil () => ()
// end of [printf_c_argtypes_free]

(* ****** ****** *)

#define __LS_none 0
#define __LS_h    1
#define __LS_hh   2
#define __LS_j    3
#define __LS_l    4
#define __LS_ll   5
#define __LS_L    6
#define __LS_t    7
#define __LS_z    8

extern
fun string_contain_char
  (s: string, c: char): bool = "atsopt_printf_c_string_find_char"
// end of [string_contain_char]

%{^

static inline
ats_bool_type
atsopt_printf_c_string_find_char (
  ats_ptr_type s, ats_char_type c
) {
  void *ans = strchr (s, c) ;
  return (ans ? ats_true_bool : ats_false_bool) ;
} // end of [ats_printf_c_string_find_char]

%} // end of ...

exception Illegal_printf_c_string

fn spec2type_translate
  (sp: char, ls: int): printf_c_argtype = case+ sp of
  | _ when sp = 'a' => FAT_c_double
  | _ when sp = 'A' => FAT_c_double
  | _ when sp = 'c' => FAT_c_char
  | _ when sp = 'd' orelse sp = 'i' => begin
      case+ ls of
      | _ when ls = __LS_h => FAT_c_int_short
      | _ when ls = __LS_hh => FAT_c_int_short_short
      | _ when ls = __LS_l => FAT_c_int_long
      | _ when ls = __LS_ll => FAT_c_int_long_long
      | _ => FAT_c_int
    end
  | _ when string_contain_char ("eEfFgG", sp) => begin
      if ls = __LS_L then FAT_c_double_long else FAT_c_double
    end
  | _ when string_contain_char ("ouxX", sp) => begin
      case+ ls of
      | _ when ls = __LS_h => FAT_c_uint_short
      | _ when ls = __LS_hh => FAT_c_uint_short_short
      | _ when ls = __LS_l => FAT_c_uint_long
      | _ when ls = __LS_ll => FAT_c_uint_long_long
      | _ => FAT_c_uint
    end
  | _ when sp = 'p' => FAT_c_ptr
  | _ when sp = 's' => FAT_c_string
  | _ => begin
      prerr "INTERNAL ERROR (ats_printf_c)";
      prerr ": spec2type_translats: illegal arguments: sp = ";
      prerr sp; prerr_newline ();
      prerr "INTERNAL ERROR (ats_printf_c)";
      prerr ": spec2type_translats: illegal arguments: ls = ";
      prerr ls; prerr_newline ();
      $Err.abort ()
    end // end of [_]
// end of [spec2type_translate]

val the_legal_prec_string: string = "aAdeEfFgGiosuxX"
val the_legal_group_string: string = "dfFgGiu"
val the_legal_alter_string: string = "aAfFeEgGxX"
val the_legal_zero_string: string = "aAdeEfFgGiouxX"

fun flagstr_verify {n,i:nat | i <= n}
  (spec: char, flagstr: string n, i: size_t i): bool = begin
  if string_is_at_end (flagstr, i) then true else let
    val flag = flagstr[i]
  in
    case+ flag of
    | _ when (flag = '+' orelse flag = '-' orelse flag = ' ') =>
        flagstr_verify (spec, flagstr, i + 1)
    | _ when (flag = '\'') => begin
        if string_contain_char (the_legal_group_string, spec) then
          flagstr_verify (spec, flagstr, i + 1)
        else false
      end
    | _ when (flag = '#') => begin
        if string_contain_char (the_legal_alter_string, spec) then
          flagstr_verify (spec, flagstr, i + 1)
        else false
      end
    | _ when (flag = '0') => begin
        if string_contain_char (the_legal_zero_string, spec) then
          flagstr_verify (spec, flagstr, i + 1)
        else false
      end
    | _ => false
   end // end of [if]
end // end of [flagstr_verify]

fn precstr_verify
  (spec: char, precstr: string): bool = let
  val precstr = string1_of_string precstr
in
  if string_is_empty precstr then true else begin
    string_contain_char (the_legal_prec_string, spec)
  end // end of [if]
end // end of [precstr_verify]

fn lenstr_translate
  (len: string): int = begin case+ len of
  | _ when len = "" => __LS_none
  | _ when len = "h" => __LS_h
  | _ when len = "hh" => __LS_hh
  | _ when len = "j" => __LS_j
  | _ when len = "l" => __LS_l
  | _ when len = "ll" => __LS_ll
  | _ when len = "L" => __LS_L
  | _ when len = "t" => __LS_t
  | _ when len = "z" => __LS_z
  | _ => $raise Illegal_printf_c_string ()
end // end of [lenstr_translate]

fn lenint_verify (spec: char, len: int): bool = let
  val ok1_string = "diouxX"
  val ok2_string = "aAcdeEfFgGiosuxX"
  val ok3_string = "aAeEfFgG"
in
  case+ len of
  | _ when len = __LS_none => true
  | _ when len = __LS_h => string_contain_char (ok1_string, spec)
  | _ when len = __LS_hh => string_contain_char (ok1_string, spec)
  | _ when len = __LS_l => string_contain_char (ok2_string, spec)
  | _ when len = __LS_ll => string_contain_char (ok1_string, spec)
  | _ when len = __LS_L => string_contain_char (ok3_string, spec)
  | _ when len = __LS_j => string_contain_char (ok1_string, spec)
  | _ when len = __LS_t => string_contain_char (ok1_string, spec)
  | _ when len = __LS_z => string_contain_char (ok1_string, spec)
  | _ => false
end // end of [lenint_verify]

fn printf_c_output (
   flagstr: string // flag string
 , width: string // [width] is unused
 , precstr: string // precision string
 , lenstr: string // length string
 , spec: char // special character
 ) : Option_vt (printf_c_argtype) = let
  var err: int = 0
  val flagstr = string1_of_string flagstr
  val ans = flagstr_verify (spec, flagstr, 0)
  val () = if (~ans) then (err := err + 1)
  val ans = precstr_verify (spec, precstr)
  val () = if (~ans) then (err := err + 1)
  val len = lenstr_translate lenstr
  val ans = lenint_verify (spec, len)
  val () = if (~ans) then (err := err + 1)
in
  if err > 0 then None_vt () else begin
    Some_vt (spec2type_translate (spec, len))
  end // end of [if]
end // end of [printf_c_output]

(* ****** ****** *)

extern fun MAIN
  (ts: printf_c_argtypes, err: &int): printf_c_argtypes

fn MAIN_lexing_error (ts: printf_c_argtypes, err: &int)
  : printf_c_argtypes = (printf_c_argtypes_free ts; lexing_error ())

fn MAIN_ (
    ot: Option_vt printf_c_argtype
  , ts: printf_c_argtypes
  , err: &int
  ) : printf_c_argtypes = begin case+ ot of
  | ~Some_vt t => MAIN (list_vt_cons (t, ts), err)
  | ~None_vt _ => (err := err + 1; ts)
end // end of [MAIN_]

(* ****** ****** *)

extern fun FLAGSTR ()
  : Option_vt (printf_c_argtype)

fn FLAGSTR_lexing_error ()
  : Option_vt (printf_c_argtype) =
  lexing_error ()

extern fun WIDTHSTR (f: string)
  : Option_vt (printf_c_argtype)
fn WIDTHSTR_lexing_error (f: string)
  : Option_vt (printf_c_argtype) =
  lexing_error ()

extern fun PRECSTR (f: string, w: string)
  : Option_vt (printf_c_argtype)
fn PRECSTR_lexing_error (f: string, w: string)
  : Option_vt (printf_c_argtype) =
  lexing_error ()

extern
fun LENSTR (f: string, w: string, p: string)
  : Option_vt (printf_c_argtype)
fn LENSTR_lexing_error
  (f: string, w: string, p: string)
  : Option_vt (printf_c_argtype) =
  lexing_error ()

extern
fun SPECHR (f: string, w: string, p: string, l: string)
  : Option_vt (printf_c_argtype)
fn SPECHR_lexing_error
  (f: string, w: string, p: string, l: string)
  : Option_vt (printf_c_argtype) =
  lexing_error ()
// end of [SPECHR_lexing_error]

(* ****** ****** *)

val __MAIN_transition_table: transition_table_t = __transition_table_make 6 "\
\000\004\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\003\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\
\000\000\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\006\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\006\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __MAIN_accept_table: accept_table_t = __accept_table_make 6 5 "\
\000\004\000\003\
\000\002\000\002\
\000\001\000\002\
\000\003\000\001\
\000\005\000\002\
"

implement MAIN (ts, err) =
case+ lexing_engine (__MAIN_transition_table, __MAIN_accept_table) of
  | 1 => (  MAIN_ (FLAGSTR (), ts, err)  )
  | 2 => (  MAIN (ts, err)  )
  | 3 => (  ts  )
  | 4 => (  (err := err + 1; ts)  )
  | _ => MAIN_lexing_error (ts, err)

val __FLAGSTR_transition_table: transition_table_t = __transition_table_make 1 "\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\001\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __FLAGSTR_accept_table: accept_table_t = __accept_table_make 1 1 "\
\000\001\000\001\
"

implement FLAGSTR () =
case+ lexing_engine (__FLAGSTR_transition_table, __FLAGSTR_accept_table) of
  | 1 => (  WIDTHSTR (lexeme_string ())  )
  | _ => FLAGSTR_lexing_error ()

val __WIDTHSTR_transition_table: transition_table_t = __transition_table_make 3 "\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\003\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __WIDTHSTR_accept_table: accept_table_t = __accept_table_make 3 3 "\
\000\003\000\001\
\000\001\000\001\
\000\002\000\001\
"

implement WIDTHSTR (f) =
case+ lexing_engine (__WIDTHSTR_transition_table, __WIDTHSTR_accept_table) of
  | 1 => (  PRECSTR (f, lexeme_string ())  )
  | _ => WIDTHSTR_lexing_error (f)

val __PRECSTR_transition_table: transition_table_t = __transition_table_make 4 "\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __PRECSTR_accept_table: accept_table_t = __accept_table_make 4 4 "\
\000\004\000\001\
\000\001\000\001\
\000\002\000\001\
\000\003\000\001\
"

implement PRECSTR (f, w) =
case+ lexing_engine (__PRECSTR_transition_table, __PRECSTR_accept_table) of
  | 1 => (  LENSTR (f, w, lexeme_string ())  )
  | _ => PRECSTR_lexing_error (f, w)

val __LENSTR_transition_table: transition_table_t = __transition_table_make 4 "\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\002\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __LENSTR_accept_table: accept_table_t = __accept_table_make 4 4 "\
\000\002\000\001\
\000\003\000\001\
\000\004\000\001\
\000\001\000\001\
"

implement LENSTR (f, w, p) =
case+ lexing_engine (__LENSTR_transition_table, __LENSTR_accept_table) of
  | 1 => (  SPECHR (f, w, p, lexeme_string ())  )
  | _ => LENSTR_lexing_error (f, w, p)

val __SPECHR_transition_table: transition_table_t = __transition_table_make 3 "\
\000\000\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\003\000\002\000\002\000\002\000\003\000\003\000\003\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\003\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\003\000\002\000\003\000\003\000\003\000\003\000\003\000\002\000\003\000\002\000\002\000\002\000\002\000\002\000\003\000\003\000\002\000\002\000\003\000\002\000\003\000\002\000\002\000\003\000\003\000\002\000\002\000\002\000\002\000\002\000\002\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
"
val __SPECHR_accept_table: accept_table_t = __accept_table_make 3 2 "\
\000\003\000\001\
\000\002\000\002\
"

implement SPECHR (f, w, p, l) =
case+ lexing_engine (__SPECHR_transition_table, __SPECHR_accept_table) of
  | 1 => (  printf_c_output (f, w, p, l, lexeme_get 0)  )
  | 2 => (  None_vt ()  )
  | _ => SPECHR_lexing_error (f, w, p, l)



// postamble

implement printf_c_string_parse (fmt) = let
  val (pf_infil |infil) = infile_make_string (fmt)
  val (pf_lexbuf | lexbuf) = lexbuf_make_infile (pf_infil | infil)
  val () = lexing_lexbuf_set (pf_lexbuf | lexbuf)
  var err: int = 0
  val ans = MAIN (list_vt_nil (), err)
  val () = lexing_lexbuf_free ()
in
  if err > 0 then begin
    printf_c_argtypes_free ans; None_vt ()
  end else begin
    Some_vt ($Lst.list_vt_reverse ans)
  end // end of [if]
end // end of [printf_c_string_parser]

(* ****** ****** *)

(* end of [ats_printf_c.lats] *)
