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

// some proofs involving view containment.

(* ****** ****** *)

implement vcontain_p_refl () = vcontain_p (lam x => (x, ()))
implement vcontain_p_trans {V1,V2,V3} (pf1, pf2) =
  let
     prval vcontain_p fpf1 = pf1
     prval vcontain_p fpf2 = pf2
     prfn fpf3 (x1: V1): [V:view] (V3, V) =
       let
          prval (x2, y2) = fpf1 x1
          prval (x3, y3) = fpf2 x2
       in
          (x3, (y2, y3))
       end
  in
     vcontain_p (fpf3)
  end

(* ****** ****** *)

implement vcontain_p_tuple_2_1 {V1,V2} () =
  vcontain_p (lam @(x1:V1, x2:V2) => (x1, x2))
implement vcontain_p_tuple_2_2 {V1,V2} () =
  vcontain_p (lam @(x1:V1, x2:V2) => (x2, x1))

(* ****** ****** *)

(* end of [vcontain.dats] *)
