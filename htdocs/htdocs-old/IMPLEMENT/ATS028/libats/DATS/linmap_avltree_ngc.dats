(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(*
**
** A map implementation based on AVL trees
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010 // based on a version done in October, 2008
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time
#define ATS_DYNLOADFLAG 0 // no dynamic loading at run-time

(* ****** ****** *)

staload "libats/SATS/linmap_avltree.sats"

(* ****** ****** *)
//
// a specialized version can be implemented on the spot
//
implement{key}
compare_key_key (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)
//
// HX-2010-03-24: this seems to work best!
//
#define HTDF 1 // max height difference
#define HTDF1 %(HTDF+1)
#define HTDF_1 %(HTDF-1)

(* ****** ****** *)

dataviewtype
avltree (
  key:t@ype, itm:viewt@ype+, int(*height*)
) =
  | {hl,hr:nat | hl <= hr+HTDF; hr <= hl+HTDF}
    B (key, itm, 1+max(hl,hr)) of
      (int (1+max(hl,hr)), key, itm, avltree (key, itm, hl), avltree (key, itm, hr))
  | E (key, itm, 0)
// end of [datatype avltree]
typedef avltree0 = avltree (void, void, 0)?

(* ****** ****** *)

staload M = "libats/ngc/SATS/linmap_avltree.sats"
staload _(*anon*) = "libats/ngc/DATS/linmap_avltree.dats"

(* ****** ****** *)

extern
castfn
decode {
  key:t0p;itm:vt0p
} {h:int} {ll,lr,l0:addr} (
  pf: $M.avlnode_v (key, itm, h, ll, lr, l0) | p0: ptr l0
) :<> B_pstruct (int(h), key, itm, ptr ll, ptr lr)

extern
prfun
encode {
  key:t0p;itm:vt0p
} {h:int} {ll,lr,l0:addr}
  {l_h,l_k,l_x,l_tl,l_tr:addr} (
  pfh: int h @ l_h
, pfk: key@l_k, pfx: itm@l_x
, pftl: ptr ll @ l_tl, pftr: ptr lr @ l_tr
| t: B_unfold (l_h, l_k, l_x, l_tl, l_tr)
) :<> $M.avlnode_v (key, itm, h, ll, lr, l0)

(* ****** ****** *)

implement{key,itm}
$M.avlnode_get_height
  {h}{ll,lr,l0}
  (pf | p) = h where {
  val t = decode (pf | p)
  val+ B (!p_h, !p_k, !p_x, !p_tl, !p_tr) = t
  val h = !p_h
  prval () = pf := encode (view@ !p_h, view@ !p_k, view@ !p_x, view@ !p_tl, view@ !p_tr | t)
} // end of [$M.avlnode_get_height]

implement{key,itm}
$M.avlnode_set_height
  {h,h1}{ll,lr,l0}
  (pf | p, h1) = () where {
  val t = decode (pf | p)
  val+ B (!p_h, !p_k, !p_x, !p_tl, !p_tr) = t
  val () = !p_h := h1
  prval () = pf := encode (view@ !p_h, view@ !p_k, view@ !p_x, view@ !p_tl, view@ !p_tr | t)
} // end of [$M.avlnode_get_height]

(* ****** ****** *)

implement{key,itm}
$M.avlnode_get_left
  {h}{ll,lr,l0}
  (pf | p) = p1_tl where {
  val t = decode (pf | p)
  val+ B (!p_h, !p_k, !p_x, !p_tl, !p_tr) = t
  val p1_tl = !p_tl
  prval () = pf := encode (view@ !p_h, view@ !p_k, view@ !p_x, view@ !p_tl, view@ !p_tr | t)
} // end of [$M.avlnode_get_left]

implement{key,itm}
$M.avlnode_set_left
  {h}{ll,lr,l0,ll1}
  (pf | p, p1_tl) = () where {
  val t = decode (pf | p)
  val+ B (!p_h, !p_k, !p_x, !p_tl, !p_tr) = t
  val () = !p_tl := p1_tl
  prval () = pf := encode (view@ !p_h, view@ !p_k, view@ !p_x, view@ !p_tl, view@ !p_tr | t)
} // end of [$M.avlnode_set_left]

(* ****** ****** *)

implement{key,itm}
$M.avlnode_get_right
  {h}{ll,lr,l0}
  (pf | p) = p1_tr where {
  val t = decode (pf | p)
  val+ B (!p_h, !p_k, !p_x, !p_tl, !p_tr) = t
  val p1_tr = !p_tr
  prval () = pf := encode (view@ !p_h, view@ !p_k, view@ !p_x, view@ !p_tl, view@ !p_tr | t)
} // end of [$M.avlnode_get_right]

implement{key,itm}
$M.avlnode_set_right
  {h}{ll,lr,l0,lr1}
  (pf | p, p1_tr) = () where {
  val t = decode (pf | p)
  val+ B (!p_h, !p_k, !p_x, !p_tl, !p_tr) = t
  val () = !p_tr := p1_tr
  prval () = pf := encode (view@ !p_h, view@ !p_k, view@ !p_x, view@ !p_tl, view@ !p_tr | t)
} // end of [$M.avlnode_set_right]

(* ****** ****** *)

(* end of [linmap_avltree.dats] *)
