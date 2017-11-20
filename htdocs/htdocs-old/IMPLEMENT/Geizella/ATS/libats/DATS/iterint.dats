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

// some common functions that iterate over integers

(* ****** ****** *)

staload "libats/SATS/iterint.sats"

(* ****** ****** *)

implement foreach_main
  {v} {vt} {n} {f} (pf | n, f, env) = let
  typedef fun_t = (!v | natLt n, !vt) -<f> void
  fun aux {i:nat | i <= n} .<n-i>.
    (pf: !v | f: fun_t, n: int n, i: int i, env: !vt):<f> void =
    if i < n then (f (pf | i, env); aux (pf | f, n, i+1, env))
    else ()
in
  aux (pf | f, n, 0, env)
end // end of [foreach_main]

// implement foreach_fun (n, f) =

implement foreach_cloptr {n} {f:eff} (n, f) = let
  viewtypedef cloptr_t = (natLt n) -<cloptr,f> void
  fn app (pf: !unit_v | i: natLt n, f: !cloptr_t): void = f (i)
  prval pf = unit_v ()
  val () = foreach_main {unit_v} {cloptr_t} {n} {f} (pf | n, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [foreach_cloptr]

(* ****** ****** *)

implement foreach2_main
  {v} {vt} {m,n} {f} (pf | m, n, f, env) = let
  viewtypedef fun_t = (!v | natLt m, natLt n, !vt) -<f> void
  fn* aux1 {i:nat | i <= m} .<m-i,n+1>.
    (pf: !v | f: fun_t, m: int m, n: int n, i: int i, env: !vt):<f> void =
    if i < m then aux2 (pf | f, m, n, i, 0, env) else ()
  and aux2 {i,j:nat | i < m; j <= n} .<m-i,n-j>.
    (pf: !v | f: fun_t, m: int m, n: int n, i: int i, j: int j, env: !vt)
    :<f> void =
    if j < n then begin
      (f (pf | i, j, env); aux2 (pf | f, m, n, i, j+1, env))
    end else begin
      aux1 (pf | f, m, n, i+1, env)
    end
in
   aux1 (pf | f, m, n, 0, env)
end // end of [foreach2_main]

// implement foreach2_fun (m, n, f) =

implement foreach2_cloptr {m,n} {f:eff} (m, n, f) = let
  viewtypedef cloptr_t = (natLt m, natLt n) -<cloptr,f> void
  fn app (pf: !unit_v | i: natLt m, j: natLt n, f: !cloptr_t)
    :<f> void = f (i, j)
  prval pf = unit_v ()
  val () = foreach2_main {unit_v} {cloptr_t} (pf | m, n, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [foreach2_cloptr]

(* ****** ****** *)

implement repeat_main
  {v} {vt} {n} {f} (pf | n, f, env) = let
  typedef fun_t = (!v | !vt) -<f> void
  fun aux {i:nat | i <= n} .<i>.
    (pf: !v | f: fun_t, i: int i, env: !vt):<f> void =
    if i > 0 then (f (pf | env); aux (pf | f, i-1, env))
    else ()
in
  aux (pf | f, n, env)
end // end of [repeat_main]

// implement repeat_fun = repeat_main<void>

implement repeat_cloptr {n} {f} (n, f) = let
  viewtypedef cloptr_t = () -<cloptr,f> void
  fn app (pf: !unit_v | f: !cloptr_t):<f> void = f ()
  prval pf = unit_v ()
  val () = repeat_main {unit_v} {cloptr_t} (pf | n, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [repeat_cloptr]

(* ****** ****** *)

(* end of [iterint.dats] *)
