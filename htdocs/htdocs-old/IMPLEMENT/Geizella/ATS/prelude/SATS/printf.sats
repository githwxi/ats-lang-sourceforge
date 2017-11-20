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

(* author: Rick Lavoie (coldfury AT cs DOT bu DOT edu) *)
(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [printf.sats] starts!\n"

#endif

(* ****** ****** *)

fun fprintf_err {m:file_mode} {ts:types}
  (pf: file_mode_lte (m, w) | out: &FILE m, fmt: printf_c ts, arg: ts)
  :<!ref> int
  = "atspre_fprintf_err"

fun fprintf {m:file_mode} {ts:types}
  (pf: file_mode_lte (m, w) | out: &FILE m, fmt: printf_c ts, arg: ts)
  :<!exnref> void
  = "atspre_fprintf"

fun printf_err {ts:types} (fmt: printf_c ts, arg: ts):<!ref> int
  = "atspre_printf_err"

fun printf {ts:types} (fmt: printf_c ts, arg: ts):<!exnref> void
  = "atspre_printf"

fun prerrf {ts:types} (fmt: printf_c ts, arg: ts):<!exnref> void
  = "atspre_prerrf"

fun assert_prerrf {b:bool} {ts:types}
  (assertion: bool b, fmt: printf_c ts, arg: ts)
  :<!exnref> [b] void
  = "atspre_assert_prerrf"

(* ****** ****** *)

fun tostringf_size {ts:types}
  (guess: Nat, fmt: printf_c ts, rest: ts):<> String
  = "atspre_tostringf_size"

fun tostringf {ts:types} (fmt: printf_c ts, rest: ts):<> String
  = "atspre_tostringf"

fun sprintf {ts:types} (fmt: printf_c ts, rest: ts):<> String
  = "atspre_tostringf"

(* ****** ****** *)

// ATS format string

typedef printf_spec_t = Nat
typedef printf_length_t = Nat
typedef printf_flags_t = Nat
typedef printf_width_t = intGte ~1
typedef printf_prec_t = intGte ~1

typedef
fprintf_ats_t0ype_type (a:t@ype) = {m:file_mode}
  (file_mode_lte (m, w) |
   &FILE m,
   printf_spec_t,
   printf_length_t,
   printf_flags_t,
   printf_width_t,
   printf_prec_t,
   a) -<fun1> void

val fprintf_ats_char : fprintf_ats_t0ype_type char
val fprintf_ats_double : fprintf_ats_t0ype_type double
val fprintf_ats_int : fprintf_ats_t0ype_type int
val fprintf_ats_ptr : fprintf_ats_t0ype_type ptr
val fprintf_ats_string : fprintf_ats_t0ype_type string
val fprintf_ats_uint : fprintf_ats_t0ype_type uint

datatype printf_ats (init:view, viewt@ype) =
 | FMT_init (init, (init | void))
 | {a:viewt@ype} FMT_int (init, int -<lin1> a) of
     (printf_spec_t,
      printf_length_t,
      printf_flags_t,
      printf_width_t,
      printf_prec_t,
      printf_ats (init, a))
 | {a:viewt@ype} FMT_uint (init, uint -<lin1> a) of
     (printf_spec_t,
      printf_length_t,
      printf_flags_t,
      printf_width_t,
      printf_prec_t,
      printf_ats (init, a))
 | {a:viewt@ype} FMT_ptr (init, ptr -<lin1> a) of
     (printf_spec_t,
      printf_length_t,
      printf_flags_t,
      printf_width_t,
      printf_prec_t,
      printf_ats (init, a))
 | {a:viewt@ype} FMT_double (init, double -> a) of
     (printf_spec_t,
      printf_length_t,
      printf_flags_t,
      printf_width_t,
      printf_prec_t,
      printf_ats (init, a))
 | {a:viewt@ype} FMT_char (init, char -> a) of
     (printf_spec_t,
      printf_length_t,
      printf_flags_t,
      printf_width_t,
      printf_prec_t,
      printf_ats (init, a))
 | {a:viewt@ype} FMT_string (init, string -> a) of
     (printf_spec_t,
      printf_length_t,
      printf_flags_t,
      printf_width_t,
      printf_prec_t,
      printf_ats (init, a))
 | {a:viewt@ype} FMT_literal (init, a) of (string, printf_ats (init, a))
 | {arg:type} {a:viewtype} FMT_apply (init, (arg -> void) -<lin1> arg -<lin1> a) of
     (printf_spec_t,
      printf_length_t,
      printf_flags_t,
      printf_width_t,
      printf_prec_t,
      printf_ats (init, a))

//

val fprintf_ats : {m:file_mode} {l_file:addr}
  (FILE m @ l_file, file_mode_lte (m, w) | ptr l_file) -<fun1>
    {a:viewtype} printf_ats (FILE m @ l_file, a) -<lin1> a

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [printf.sats] finishes!\n"

#endif

(* end of [printf.sats] *)
