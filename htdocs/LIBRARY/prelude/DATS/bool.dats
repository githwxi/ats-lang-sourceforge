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
** $PATSHOME/prelude/DATS/CODEGEN/bool.atxt
** Time of generation: Fri Feb 28 17:55:13 2014
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: Feburary, 2012 *)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at run-time

(* ****** ****** *)

(*
//
// HX: see CATS/bool.cats
//
implement
tostring_bool
  (b) = if b then "true" else "false"
// end of [tostring_bool]
*)

implement
tostring_val<bool> = tostring_bool

(* ****** ****** *)

(*
//
// HX: see CATS/bool.cats
//
implement
fprint_bool (out, x) =
  fprint_string (out, tostring_bool (x))
// end of [fprint_bool]
*)

implement fprint_val<bool> = fprint_bool

(* ****** ****** *)

(* end of [bool.dats] *)
