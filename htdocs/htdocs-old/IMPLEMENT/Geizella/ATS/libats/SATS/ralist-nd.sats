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

// An implementation of random-access list based on nested datatypes

(* ****** ****** *)

// assumed in [libats/DATS/ralist-nd.dats]
abstype ralist (a:type+, int) // boxed type

(* ****** ****** *)

exception RandomAccessListSubscriptException

fun ralist_length {a:type} {n:nat} (xs: ralist (a, n)):<> int n

fun ralist_head {a:type} {n:pos} (xs: ralist (a, n)):<> a
fun ralist_head_exn {a:type} {n:nat} (xs: ralist (a, n)):<!exn> a

fun ralist_tail {a:type} {n:pos}
  (xs: ralist (a, n)):<> ralist (a, n-1)
fun ralist_tail_exn {a:type} {n:nat}
  (xs: ralist (a, n)):<!exn> [n>0] ralist (a, n-1)

fun ralist_cons {a:type} {n:nat}
  (x: a, xs: ralist (a, n)):<> ralist (a, n+1)

fun ralist_uncons {a:type} {n:pos}
  (xs: ralist (a, n)):<> @(a, ralist (a, n-1))
fun ralist_uncons_exn {a:type} {n:pos}
  (xs: ralist (a, n)):<!exn> [n>0] @(a, ralist (a, n-1))

fun ralist_lookup {a:type} {n:nat}
  (xs: ralist (a, n), i: natLt n):<> a
fun ralist_lookup_exn {a:type} {n:nat}
  (xs: ralist (a, n), i: Nat):<!exn> a

fun ralist_update {a:type} {n:nat}
  (xs: ralist (a, n), i: natLt n, x: a):<> ralist (a, n)
fun ralist_update_exn {a:type} {n:nat}
  (xs: ralist (a, n), i: Nat, x: a):<!exn> ralist (a, n)

(* ****** ****** *)

(* end of [ralist-nd.sats] *)
