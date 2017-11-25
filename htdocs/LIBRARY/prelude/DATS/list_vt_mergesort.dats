(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2010-2013 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
**
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
**
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(*
** Source:
** $PATSHOME/prelude/DATS/CODEGEN/list_vt_mergesort.atxt
** Time of generation: Fri Feb 28 17:55:25 2014
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: Feburary, 2012 *)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

implement{a}
list_vt_mergesort$cmp
  (x1, x2) = gcompare_ref<a> (x1, x2)
// end of [list_vt_mergesort$cmp]

implement{a}
list_vt_mergesort
  {n} (xs) = let
//
fun split
  {n,n1:nat | n >= n1} .<n1>.
(
  xs: &list_vt (a, n) >> list_vt (a, n1)
, n1: int n1, res: &List_vt a? >> list_vt (a, n-n1)
) :<!wrt> void = let
in
//
if n1 > 0 then let
  val+@list_vt_cons (_, xs1) = xs
  val () = split (xs1, n1-1, res)
in
  fold@ (xs)
end else let
  val () = res := xs
  val () = xs := list_vt_nil ()
in
  // nothing
end // end of [if]
//
end // end of [split]
//
fun merge {n1,n2:nat} .<n1+n2>.
(
  xs1: list_vt (a, n1)
, xs2: list_vt (a, n2)
, res: &List_vt a? >> list_vt (a, n1+n2)
) :<!wrt> void = let
in
//
case+ xs1 of
| @list_vt_cons
    (x1, xs11) => (
    case+ xs2 of
    | @list_vt_cons
        (x2, xs21) => let
        val sgn =
          list_vt_mergesort$cmp<a> (x1, x2)
        // end of [val]
      in
        if sgn <= 0 then let
          prval () = fold@{a}(xs2)
          val () = merge (xs11, xs2, xs11)
          prval () = fold@{a}(xs1)
        in
          res := xs1
        end else let
          prval () = fold@{a}(xs1)
          val () = merge (xs1, xs21, xs21)
          prval () = fold@{a}(xs2)
        in
          res := xs2
        end // end of [if]
      end // end of [list_vt_cons]
    | ~list_vt_nil () => (fold@ (xs1); res := xs1)
  ) // end of [list_vt_cons]
| ~list_vt_nil () => (res := xs2)
//
end // end of [merge]
//
val n = list_vt_length<a> (xs)
//
in
//
if n >= 2 then let
  val+@list_vt_cons (_, xs1) = xs
  var res: List_vt a? // uninitialized
  val () = split (xs1, half(n-1), res)
  prval () = fold@ (xs)
  val xs1 = list_vt_mergesort<a> (xs)
  val xs2 = list_vt_mergesort<a> (res)
  val () = merge (xs1, xs2, res)
in
  res
end else xs // end of [if]
//
end // end of [list_vt_mergesort]

(* ****** ****** *)

implement{a}
list_vt_mergesort_fun
  (xs, cmp) = let
//
implement{a2}
list_vt_mergesort$cmp
  (x1, x2) = let
//
val cmp = $UN.cast{cmpref(a2)}(cmp) in cmp (x1, x2)
//
end (* end of [list_vt_mergesort$cmp] *)
//
in
  list_vt_mergesort<a> (xs)
end // end of [list_vt_mergesort_fun]

(* ****** ****** *)

(* end of [list_vt_mergesort.dats] *)
