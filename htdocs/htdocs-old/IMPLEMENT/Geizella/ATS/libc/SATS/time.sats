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
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
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

(* incoporating [time.h] *)

//

abst@ype time_t = $extype "ats_time_t_type"
abst@ype clock_t = $extype "ats_clock_t_type"

//

fun lint_of_time_t (t: time_t):<> int_long_t0ype
  = "atslib_lint_of_time_t"

overload lint_of with lint_of_time_t

fun double_of_time_t (t: time_t):<> double_t0ype
  = "atslib_double_of_time_t"

overload double_of with double_of_time_t

//

symintr time

fun time_get (): time_t = "atslib_time_get"
fun time_get_and_set {l:addr}
  (pf: !time_t? @ l >> time_t @ l | p: ptr l): time_t
  = "atslib_time_get_and_set"

overload time with time_get
overload time with time_get_and_set

//

fun difftime (finish: time_t, start: time_t):<> double
  = "atslib_difftime"

//

fun lint_of_clock_t (c: clock_t):<> int_long_t0ype
  = "atslib_lint_of_clock_t"

overload lint_of with lint_of_clock_t

fun double_of_clock_t (c: clock_t):<> double_t0ype
  = "atslib_double_of_clock_t"

overload double_of with double_of_clock_t

//

macdef CLOCKS_PER_SEC = $extval (int, "CLOCKS_PER_SEC")

//

fun clock (): clock_t = "atslib_clock"

(* ****** ****** *)

(* end of [time.sats] *)
