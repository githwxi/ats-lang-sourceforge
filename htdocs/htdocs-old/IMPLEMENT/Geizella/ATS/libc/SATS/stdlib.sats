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

symintr atof atoi atol atoll

//

fun atof_strbuf {m,n:nat} (sb: &strbuf (m, n)):<> double
  = "atslib_atsof"
fun atof_string (s: string):<> double = "atslib_atof"

overload atof with atof_strbuf
overload atof with atof_string

//

fun atoi_strbuf {m,n:nat} (sb: &strbuf (m, n)):<> Int
  = "atslib_atoi"
fun atoi_string (s: string):<> Int = "atslib_atoi"

overload atoi with atoi_strbuf
overload atoi with atoi_string

//

fun atol_strbuf {m,n:nat} (sb: &strbuf (m, n)):<> lint
  = "atslib_atol"
fun atol_string (s: string):<> lint = "atslib_atol"

overload atol with atol_strbuf
overload atol with atol_string

//

fun atoll_strbuf {m,n:nat} (sb: &strbuf (m, n)):<> llint
  = "atslib_atoll"
fun atoll_string (s: string):<> llint = "atslib_atoll"

overload atoll with atoll_string
overload atoll with atoll_strbuf

//

fun getenv_err (s: string):<!ref> Stropt = "atslib_getenv_opt"
fun getenv (s: string):<!ref> String = "atslib_getenv"

// a generic binary search function

fun bsearch {a:viewt@ype} {n:nat}
  (key: &a,
   base: &(@[a][n]),
   nmemb: int n,
   size: sizeof_t a,
   compar: (&a, &a) -<fun1> int)
  : intBtw (~1, n)
  = "atslib_bsearch"

//

fun qsort {a:viewt@ype} {n:nat}
  (base: &(@[a][n]),
   nmemb: int n,
   size: sizeof_t a,
   compar: (&a, &a) -<fun1> int)
  : void
  = "atslib_qsort"

(* ****** ****** *)

(* end of [stdlib.sats] *)
