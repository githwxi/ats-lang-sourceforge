(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
//
// Simple Linear Objects in ATS
//
(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)
// Start Time: November, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)

sortdef vt0p = viewt@ype

(* ****** ****** *)

absviewtype
sobjptr_viewt0ype_addr_viewtype
  (a:viewt@ype+, l:addr) // end of [sobjptr]
stadef sobjptr = sobjptr_viewt0ype_addr_viewtype
viewtypedef
sobjptr1 (a:vt0p) = [l:addr | l > null] sobjptr (a, l)

(* ****** ****** *)

prfun
sobjptr_fold
  {a:vt0p} {l:addr} (
  pfgc: free_gc_v (a?, l)
, pfat: a @ l
| x: !ptr l >> sobjptr (a, l)
) : void // end of [sobjptr_fold]

prfun
sobjptr_unfold
  {a:vt0p} {l:addr} (
  x: !sobjptr (a, l) >> ptr l
) : (free_gc_v (a?, l), a @ l)
// end of [sobjptr_unfold]

(* ****** ****** *)

castfn
ptr_of_sobjptr
  {a:vt0p} {l:addr} (x: !sobjptr (a, l)): ptr l
overload ptr_of with ptr_of_sobjptr

(* ****** ****** *)

castfn
sobjptr_encode
  {a:vt0p} {l:addr} (
  pfgc: free_gc_v (a?, l), pfat: a @ l
| p: ptr l
) : sobjptr (a, l) // end of [sobjptr_encode]

castfn
sobjptr_decode
  {a:vt0p} {l:addr} (
  x: sobjptr (a, l)
) : (
  free_gc_v (a?, l), a @ l | ptr l
) // end of [sobjptr_decode]

(* ****** ****** *)

fun{a:viewt@ype}
sobjptr_new (): sobjptr1 (a?)

fun sobjptr_free
  {a:viewt@ype} {l:addr} (x: sobjptr (a?, l)): void
// end of [sobjptr_free]

(* ****** ****** *)

(* end of [sobjptr.sats] *)
