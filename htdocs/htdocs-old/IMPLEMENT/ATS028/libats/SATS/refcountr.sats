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
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

absviewtype
nrefr_viewt0ype_viewtype (a:viewt@ype) = ptr // support reentrancy
stadef nrefr = nrefr_viewt0ype_viewtype

(* ****** ****** *)

fun{a:viewt@ype}
refcountr_make (x: a):<> nrefr (a)

fun{a:viewt@ype}
refcountr_ref (r: !nrefr a):<> nrefr a

fun{a:viewt@ype}
refcountr_unref
  (r: nrefr a, x: &a? >> opt (a, b)):<> #[b: bool] bool(b)
// end of [refcountr_unref]

fun{a:viewt@ype}
refcountr_unref_fun
  (r: nrefr a, f: (&a >> a?) -<fun> void):<> void
// end of [refcountr_unref_fun]

fun{a:viewt@ype}
refcountr_get_count (r: !nrefr a):<> uint

(* ****** ****** *)

absviewtype
nrefrout (a:viewt@ype, l:addr) = nrefr (a)

prfun refcountr_addback
  {a:viewt@ype} {l:addr}
  (pf: a @ l | r: !nrefrout (a, l) >> nrefr (a)): void
// end of [refcountr_addback]

fun{a:viewt@ype}
refcountr_takeout
  (r: !nrefr a >> nrefrout (a, l)):<> #[l:addr] (a @ l | ptr l)
// end of [refcountr_takeout]

(* ****** ****** *)

(* end of [refcountr.sats] *)
