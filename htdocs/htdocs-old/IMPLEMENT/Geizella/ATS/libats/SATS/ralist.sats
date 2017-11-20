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

// assumed in [libats/DATS/ralist.dats]
abstype ralist (a:t@ype+, int) // boxed type

(* ****** ****** *)

exception RandomAccessListSubscriptException

fun{a:t@ype} ralist_length {n:nat} (xs: ralist (a, n)):<> int n

fun{a:t@ype} ralist_head {n:pos} (xs: ralist (a, n)):<> a
fun{a:t@ype} ralist_head_exn {n:nat} (xs: ralist (a, n)):<!exn> a

fun{a:t@ype} ralist_tail {n:pos}
  (xs: ralist (a, n)):<> ralist (a, n-1)
fun{a:t@ype} ralist_tail_exn {n:nat}
  (xs: ralist (a, n)):<!exn> [n>0] ralist (a, n-1)

fun{a:t@ype} ralist_cons {n:nat}
  (x: a, xs: ralist (a, n)):<> ralist (a, n+1)
fun{a:t@ype} ralist_uncons {n:pos}
  (xs: ralist (a, n)):<> @(a, ralist (a, n-1))
fun{a:t@ype} ralist_uncons_exn {n:pos}
  (xs: ralist (a, n)):<!exn> [n>0] @(a, ralist (a, n-1))

fun{a:t@ype} ralist_last {n:pos} (xs: ralist (a, n)):<> a
fun{a:t@ype} ralist_last_exn {n:nat} (xs: ralist (a, n)):<!exn> a

// taking the first (n-1) elements
fun{a:t@ype} ralist_init {n:pos}
  (xs: ralist (a, n)):<> ralist (a, n-1)
fun{a:t@ype} ralist_init_exn {n:nat}
  (xs: ralist (a, n)):<!exn> [n>0] ralist (a, n-1)

fun{a:t@ype} ralist_snoc {n:nat}
  (x: a, xs: ralist (a, n)):<> ralist (a, n+1)
fun{a:t@ype} ralist_unsnoc {n:pos}
  (xs: ralist (a, n)):<> @(ralist (a, n-1), a)
fun{a:t@ype} ralist_unsnoc_exn {n:pos}
  (xs: ralist (a, n)):<!exn> [n>0] @(ralist (a, n-1), a)

fun{a:t@ype} ralist_lookup {n:nat}
  (xs: ralist (a, n), i: natLt n):<> a
fun{a:t@ype} ralist_lookup_exn {n:nat}
  (xs: ralist (a, n), i: Nat):<!exn> a

fun{a:t@ype} ralist_update {n:nat}
  (xs: ralist (a, n), i: natLt n, x: a):<> ralist (a, n)
fun{a:t@ype} ralist_update_exn {n:nat}
  (xs: ralist (a, n), i: Nat, x: a):<!exn> ralist (a, n)

(* ****** ****** *)

// end of ralist.sats
