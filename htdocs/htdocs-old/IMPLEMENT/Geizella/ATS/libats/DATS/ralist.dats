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

staload "libats/SATS/ralist.sats"

datatype T (a:t@ype+, int) =
  | RAnil (a, 0)
  | RAone (a, 1) of a
  | {n:pos} RAeven (a, n+n) of (T (a, n), T (a, n))
  | {n:pos} RAodd (a, n+n+1) of (T (a, n+1), T (a, n))

assume ralist (a:t@ype, n:int) = T (a, n)

(* ****** ****** *)

implement ralist_length (xs) = case+ xs of
  | RAnil () => 0 | RAone _ => 1
  | RAeven (xs, _) => 2 * ralist_length (xs)
  | RAodd (_, ys) => 2 * ralist_length (ys) + 1

(* ****** ****** *)

extern fun{a:t@ype} raeven {n:nat}
  (xs: ralist (a, n), ys: ralist (a, n)):<> ralist (a, n+n)

implement raeven (xs, ys) = case+ xs of
  | RAnil () => ys | _ =>> RAeven (xs, ys)

extern fun{a:t@ype} raodd {n:nat}
  (xs: ralist (a, n+1), ys: ralist (a, n)):<> ralist (a, n+n+1)

implement raodd (xs, ys) = case+ xs of
  | RAone _ => xs | _ =>> RAodd (xs, ys)

(* ****** ****** *)

implement ralist_cons (x, xs) = case+ xs of
  | RAnil () => RAone x
  | RAone _ => RAeven (RAone x, xs)
  | RAeven (ys, zs) => RAodd (ralist_cons (x, zs), ys)
  | RAodd (ys, zs) => RAeven (ralist_cons (x, zs), ys)

(* ****** ****** *)

implement ralist_head (xs) = case+ xs of
  | RAone x => x
  | RAeven (xs, _) => ralist_head xs
  | RAodd (xs, _) => ralist_head xs


implement ralist_head_exn (xs) = case+ xs of
  | RAnil () => begin
      $raise RandomAccessListSubscriptException ()
    end
  | _ =>> ralist_head xs

(* ****** ****** *)

implement ralist_tail (xs) = case+ xs of
  | RAone _ => RAnil
  | RAeven (xs, ys) => raodd (ys, ralist_tail xs)
  | RAodd (xs, ys) => raeven (ys, ralist_tail xs)

implement ralist_tail_exn (xs) = case+ xs of
  | RAnil () => begin
      $raise RandomAccessListSubscriptException ()
    end
  | _ =>> ralist_tail xs

(* ****** ****** *)

implement ralist_uncons (xs) = case+ xs of
  | RAone x => (x, RAnil ())
  | RAeven (xs, ys) => let
      val (x, xs') = ralist_uncons xs
    in
      (x, raodd (ys, xs'))
    end
  | RAodd (xs, ys) => let
      val (x, xs') = ralist_uncons xs
    in
      (x, raeven (ys, xs'))
    end


implement ralist_uncons_exn (xs) = case+ xs of
  | RAnil () => begin
      $raise RandomAccessListSubscriptException ()
    end
  | _ =>> ralist_uncons xs

(* ****** ****** *)

implement ralist_snoc (x, xs) = case+ xs of
  | RAnil () => RAone x
  | RAone _ => RAeven (xs, RAone x)
  | RAeven (ys, zs) => RAodd (ralist_snoc (x, ys), zs)
  | RAodd (ys, zs) => RAeven (ys, ralist_snoc (x, zs))


implement ralist_last (xs) = case+ xs of
  | RAone x => x
  | RAeven (_, ys) => ralist_last ys
  | RAodd (xs, _) => ralist_last xs

implement ralist_last_exn (xs) = case+ xs of
  | RAnil () => begin
      $raise RandomAccessListSubscriptException ()
    end
  | _ =>> ralist_last xs

(* ****** ****** *)

implement ralist_init (xs) = case+ xs of
  | RAone x => RAnil
  | RAeven (xs, ys) => raodd (xs, ralist_init ys)
  | RAodd (xs, ys) => raeven (ralist_init xs, ys)

implement ralist_init_exn (xs) = case+ xs of
  | RAnil () => begin
      $raise RandomAccessListSubscriptException ()
    end
  | _ =>> ralist_init xs

(* ****** ****** *)

implement ralist_unsnoc (xs) = case+ xs of
  | RAone x => (RAnil (), x)
  | RAeven (xs, ys) => let
      val (ys, y) = ralist_unsnoc ys
    in
       (raodd (xs, ys), y)
    end
  | RAodd (xs, ys) => let
      val (xs, x) = ralist_unsnoc xs
    in
      (raeven (xs, ys), x)
    end

implement ralist_unsnoc_exn (xs) = case+ xs of
  | RAnil () => begin
      $raise RandomAccessListSubscriptException ()
    end
  | xs =>> ralist_unsnoc xs

(* ****** ****** *)

implement ralist_lookup (xs, i) = case+ xs of
  | RAone x => x
  | RAeven (xs, ys) =>
      if i nmod 2 = 0 then ralist_lookup (xs, nhalf i)
      else ralist_lookup (ys, nhalf i)
  | RAodd (xs, ys) =>
      if i nmod 2 = 0 then ralist_lookup (xs, nhalf i)
      else ralist_lookup (ys, nhalf i)

implement ralist_lookup_exn (xs, i) =
  if i < ralist_length xs then begin
    ralist_lookup (xs, i)
  end else begin
    $raise RandomAccessListSubscriptException ()
  end

(* ****** ****** *)

implement ralist_update (xs, i, x) = case+ xs of
  | RAone _ => RAone x
  | RAeven (xs, ys) =>
      if i nmod 2 = 0 then begin
        RAeven (ralist_update (xs, nhalf i, x), ys)
      end else begin
        RAeven (xs, ralist_update (ys, nhalf i, x))
      end
  | RAodd (xs, ys) =>
      if i nmod 2 = 0 then begin
        RAodd (ralist_update (xs, nhalf i, x), ys)
      end else begin
        RAodd (xs, ralist_update (ys, nhalf i, x))
      end

implement ralist_update_exn (xs, i, x) =
  if i < ralist_length xs then begin
    ralist_update (xs, i, x)
  end else begin
    $raise RandomAccessListSubscriptException ()
  end

(* ****** ****** *)

(* end of [ralist.dats] *)
