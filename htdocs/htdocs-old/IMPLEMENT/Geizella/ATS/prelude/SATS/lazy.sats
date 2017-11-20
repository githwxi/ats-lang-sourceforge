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

datatype stream_con (a:t@ype+) =
  | stream_nil (a) | stream_cons (a) of (a, stream a)

where stream (a:t@ype) = lazy (stream_con a)

(* ****** ****** *)

dataviewtype stream_vt_con (a:viewt@ype+) =
  | stream_vt_nil (a) | stream_vt_cons (a) of (a, stream_vt a)

where stream_vt (a:viewt@ype) = lazy_vt (stream_vt_con a)

(* ****** ****** *)

exception StreamSubscriptException

(* ****** ****** *)

fun{a:t@ype} stream_filter
  (xs: stream a, p: a -<cloptr1> bool): stream a

fun{a:t@ype} stream_vt_filter
  (xs: stream_vt a, p: a -<cloptr1> bool): stream_vt a

(* ****** ****** *)

fun{a,b:t@ype} stream_map
  (xs: stream a, f: a -<cloptr1> b): stream b

fun{a1,a2,b:t@ype} stream_map2
  (xs1: stream a1, xs2: stream a2, f: (a1, a2) -<cloptr1> b): stream b

(* ****** ****** *)

fun{a:t@ype} stream_merge_ord
  (xs1: stream a, xs2: stream a, lte: (a, a) -<cloptr1> bool): stream a

(* ****** ****** *)

fun{a:t@ype} stream_nth (xs: stream a, i: Nat): a

(* ****** ****** *)

(* end of [lazy.sats] *)
