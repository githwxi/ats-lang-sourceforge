(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [char.sats] starts!\n"

#endif

(* ****** ****** *)

// some common functions on characters

(* ****** ****** *)

fun char_of_int (i: int):<> char
  = "atspre_char_of_int"

fun int_of_char (c: char):<> int
  = "atspre_int_of_char"

fun uint_of_char (c: char):<> uint
  = "atspre_uint_of_char"

(* ****** ****** *)

fun sub_char_char (c1: char, c2: char):<> int
  = "atspre_sub_char_char"
overload - with sub_char_char

(* ****** ****** *)

fun lt_char_char (c1: char, c2: char):<> bool
  = "atspre_lt_char_char"
and lte_char_char (c1: char, c2: char):<> bool
  = "atspre_lte_char_char"
and gt_char_char (c1: char, c2: char):<> bool
  = "atspre_gt_char_char"
and gte_char_char (c1: char, c2: char):<> bool
  = "atspre_gte_char_char"

overload < with lt_char_char
overload <= with lte_char_char
overload > with gt_char_char
overload >= with gte_char_char

fun eq_char_char (c1: char, c2: char):<> bool
  = "atspre_eq_char_char"

and neq_char_char (c1: char, c2: char):<> bool
  = "atspre_neq_char_char"

overload = with eq_char_char
overload <> with neq_char_char

fun compare_char_char (c1: char, c2: char):<> Sgn
  = "atspre_compare_char_char"
overload compare with compare_char_char

(* ****** ****** *)

// print functions for characters

fun fprint_char {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: char):<!exnref> void
  = "atspre_fprint_char"

fun print_char (c: char):<!ref> void = "atspre_print_char"
and prerr_char (c: char):<!ref> void = "atspre_prerr_char"

overload fprint with fprint_char
overload print with print_char
overload prerr with prerr_char

// stringize

fun tostring_char (c: char):<> string (1)
  = "atspre_tostring_char"
overload tostring with tostring_char

(* ****** ****** *)

fun char_isalpha (c: char):<> bool // whether the char is in the alphabet
  = "atspre_char_isalpha"
and char_isalnum (c: char):<> bool // whether the char is in the alphanumeric
  = "atspre_char_isalnum"
and char_isascii (c: char):<> bool = "atspre_char_isascii"
and char_iscntrl (c: char):<> bool = "atspre_char_iscntrl"
and char_isdigit (c: char):<> bool // whether the char is a digit
  = "atspre_char_isdigit"
and char_isgraph (c: char):<> bool = "atspre_char_isgraph"
and char_islower (c: char):<> bool = "atspre_char_islower"
and char_isnull (c: char):<> bool = "atspre_char_isnull"
and char_isprint (c: char):<> bool = "atspre_char_isprint"
and char_ispunct (c: char):<> bool = "atspre_char_ispunct"
and char_isspace (c: char):<> bool = "atspre_char_isspace"
and char_isupper (c: char):<> bool = "atspre_char_isupper"
and char_isxdigit (c: char):<> bool // whether the char is a hex digit
  = "atspre_char_isxdigit"
and char_tolower (c: char):<> char = "atspre_char_tolower"
and char_toupper (c: char):<> char = "atspre_char_toupper"

(* ****** ****** *)

fun eq_char1_char1 {c1,c2:char}
  (c1: char c1, c2: char c2):<> bool (c1 == c2)
  = "atspre_eq_char1_char1"
and neq_char1_char1 {c1,c2:char}
  (c1: char c1, c2: char c2):<> bool (c1 <> c2)
  = "atspre_neq_char1_char1"

overload = with eq_char1_char1
overload <> with neq_char1_char1

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [char.sats] finishes!\n"

#endif

(* end of [char.sats] *)
