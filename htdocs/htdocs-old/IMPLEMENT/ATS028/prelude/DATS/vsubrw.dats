(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)
//
// HX: some proof functions involving view containment.
//
(* ****** ****** *)

staload "prelude/SATS/vsubrw.sats"

(* ****** ****** *)

assume vsubr_p
  (v1:view, v2:view) = v2 -<prf> [v:view] @(v1, v)
assume vsubw_p
  (v1:view, v2:view) = v2 -<prf> (v1, v1 -<lin,prf> v2)

(* ****** ****** *)

implement vsubr_intr (fpf) = fpf
implement vsubr_elim (fpf) = fpf

implement
vsubr_refl {v} () = lam (pf) => @(pf, unit_v ())

implement
vsubr_trans (fpf21, fpf32) = lam (pf3) => let
  val (pf2, pf32) = fpf32 (pf3); prval (pf1, pf21) = fpf21 (pf2); 
in
  (pf1, @(pf21, pf32))
end // end of [vcontain_trans]

(* ****** ****** *)

implement vsubr_of_vsubw (fpf) = lam (pf) => fpf (pf)

(* ****** ****** *)

implement
vsubr_tup_2_0 {v1,v2} () = vsubr_of_vsubw (vsubw_tup_2_0 {v1,v2} ())
implement
vsubr_tup_2_1 {v1,v2} () = vsubr_of_vsubw (vsubw_tup_2_1 {v1,v2} ())

(* ****** ****** *)

implement vsubw_intr (fpf) = fpf
implement vsubw_elim (fpf) = fpf

(* ****** ****** *)

implement
vsubw_tup_2_0 () = lam (pf) => @(pf.0, llam pf0 => (pf0, pf.1))
implement
vsubw_tup_2_1 () = lam (pf) => @(pf.1, llam pf1 => (pf.0, pf1))

(* ****** ****** *)

implement
vsubw_array_elt {a} (pf_mul) =
  lam pf_arr =<prf> array_v_takeout {a} (pf_mul, pf_arr)
// end of [vsubw_array_elt]

(* ****** ****** *)

implement
vsubw_array_subarray
  {a} {n0,i,n} (pf_mul) =
lam pf_arr =<prf> let
  prval (pf1_arr, pf2_arr) = array_v_split {a} {n0} {i} (pf_mul, pf_arr)
  prval pf2_mul = mul_istot {n, sizeof a} ()
  prval (pf21_arr, pf22_arr) = array_v_split {a} {n0-i} {n} (pf2_mul, pf2_arr)
in (
  pf21_arr
, llam pf21_arr => array_v_unsplit {a} (
    pf_mul, pf1_arr, array_v_unsplit {a} (pf2_mul, pf21_arr, pf22_arr)
  ) // end of [llam]
) end // end of [lam] // end of [vsubw_array_subarray]

(* ****** ****** *)

(* end of [vsubrw.dats] *)
