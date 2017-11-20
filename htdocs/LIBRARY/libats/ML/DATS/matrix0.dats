(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2010-2014 Hongwei Xi, ATS Trustful Software, Inc.
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

(* Author: Hongwei Xi *)
(* Authoremail: gmhwxiATgmailDOTcom *)
(* Start time: February, 2014 *)

(* ****** ****** *)

staload
UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libats/ML/SATS/basis.sats"
staload "libats/ML/SATS/matrix0.sats"

(* ****** ****** *)
//
implement{}
matrix0_of_mtrxszref{a}(A) = $UN.cast{matrix0(a)}(A)
//
implement{}
mtrxszref_of_matrix0{a}(A) = $UN.cast{mtrxszref(a)}(A)
//
(* ****** ****** *)
//
implement{
} matrix0_get_ref (M) =
  mtrxszref_get_ref (mtrxszref_of_matrix0(M))
//
implement{
} matrix0_get_nrow (M) =
  mtrxszref_get_nrow (mtrxszref_of_matrix0(M))
implement{
} matrix0_get_ncol (M) =
  mtrxszref_get_ncol (mtrxszref_of_matrix0(M))
//
(* ****** ****** *)

implement{
} matrix0_get_refsize (M) = let
  var nrow: size_t and ncol: size_t
  val Mref =
  $effmask_wrt
  (
    mtrxszref_get_refsize(mtrxszref_of_matrix0(M), nrow, ncol)
  ) (* end of [val] *)
in
  (Mref, nrow, ncol)
end // end of [matrix0_get_refsize]

(* ****** ****** *)

implement
{a}(*tmp*)
matrix0_make_elt
  (nrow, ncol, x0) =
  matrix0_of_mtrxszref (mtrxszref_make_elt<a> (nrow, ncol, x0))
// end of [matrix0_make_elt]

(* ****** ****** *)

implement{a}
matrix0_get_at_int
  (M0, i, j) = let
  val i = g1ofg0_int(i)
  and j = g1ofg0_int(j)
in
//
if i >= 0
then (
if j >= 0 then
  matrix0_get_at_size<a> (M0, i2sz(i), i2sz(j))
else
  $raise MatrixSubscriptExn((*void*)) // neg index
// end of [if]
) else
  $raise MatrixSubscriptExn((*void*)) // neg index
// end of [if]
//
end // end of [matrix0_get_at_int]

(* ****** ****** *)

implement{a}
matrix0_get_at_size
  (M0, i, j) = let
  val MSZ =
    mtrxszref_of_matrix0 (M0) in mtrxszref_get_at_size (MSZ, i, j)
  // end of [val]
end // end of [matrix0_get_at_size]

(* ****** ****** *)

implement{a}
matrix0_set_at_int
  (M0, i, j, x) = let
  val i = g1ofg0_int(i)
  and j = g1ofg0_int(j)
in
//
if i >= 0
then (
if j >= 0 then
  matrix0_set_at_size<a> (M0, i2sz(i), i2sz(j), x)
else
  $raise MatrixSubscriptExn((*void*)) (* neg index *)
// end of [if]
) else
  $raise MatrixSubscriptExn((*void*)) (* neg index *)
// end of [if]
//
end // end of [matrix0_set_at_int]

(* ****** ****** *)

implement{a}
matrix0_set_at_size
  (M0, i, j, x) = let
  val MSZ =
    mtrxszref_of_matrix0 (M0) in mtrxszref_set_at_size (MSZ, i, j, x)
  // end of [val]
end // end of [matrix0_set_at_size]

(* ****** ****** *)

implement{a}
fprint_matrix0 (out, M) =
fprint_mtrxszref (out, mtrxszref_of_matrix0 (M))

(* ****** ****** *)

implement{a}
matrix0_tabulate
  (nrow, ncol, f) = let
//
implement{a2}
matrix_tabulate$fopr
  (i, j) = $UN.castvwtp0{a2}(f(i,j))
//
val MSZ = mtrxszref_tabulate<a> (nrow, ncol)
//
in
  matrix0_of_mtrxszref (MSZ)  
end // end of [matrix0_tabulate]

(* ****** ****** *)

implement{a}
matrix0_foreach
  (M0, f) = let
//
fun loop
(
  p: ptr, i: size_t
) : void = (
if i > 0 then let
  val (pf, fpf | p) = $UN.ptr0_vtake (p)
  val ((*void*)) = f (!p)
  prval ((*void*)) = fpf (pf)
in
  loop (ptr_succ<a> (p), pred (i))
end else ((*void*)) // end of [if]
) (* end of [loop] *)
//
val (M, m, n) = matrix0_get_refsize (M0)
//
in
  loop (ptrcast(M), m * n)
end // end of [matrix0_foreach]

(* ****** ****** *)

implement{a}
matrix0_iforeach
  (M0, f) = let
//
val (M, m, n) =
  matrix0_get_refsize (M0)
//
fun loop
(
  p: ptr
, k: size_t, i: size_t, j: size_t
) : void = (
if k > 0 then let
  val (
    pf, fpf | p
  ) = $UN.ptr0_vtake (p)
  val () = f (i, j, !p)
  prval ((*void*)) = fpf (pf)
  val p = ptr_succ<a> (p)
  val k = pred(k) and j = succ(j)
in
//
if j < n
  then loop (p, k, i, j)
  else loop (p, k, succ(i), i2sz(0))
// end of [if]
//
end else ((*void*)) // end of [if]
) (* end of [loop] *)
//
in
  loop (ptrcast(M), i2sz(0), i2sz(0), m * n)
end // end of [matrix0_iforeach]

(* ****** ****** *)

(* end of [matrix.dats] *)
