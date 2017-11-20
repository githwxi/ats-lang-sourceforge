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

// An implementation of random-access list based on nested datatypes

(* ****** ****** *)

staload "libats/SATS/ralist-nd.sats"

typedef P (a:type) (b:type) = '(a, b)
macdef P x y = '(x, y)

datatype T (a:type+, int) =
  | RAnil (a, 0) | RAone (a, 1) of a
  | {n:pos} RAeven (a, n+n) of T (P a a, n)
  | {n:pos} RAodd (a, n+n+1) of (a, T (P a a, n))

assume ralist (a:type, n:int) = T (a, n)

(* ****** ****** *)

implement ralist_length (xs) = case+ xs of
  | RAnil _ => 0
  | RAone _ => 1
  | RAeven xs => 2 * ralist_length (xs)
  | RAodd (_, ys) => 2 * ralist_length (ys) + 1

(* ****** ****** *)

implement ralist_cons (x0, xs) = case+ xs of
  | RAnil _ => RAone x0
  | RAone x => RAeven (RAone (P x0 x))
  | RAeven xxs => RAodd (x0, xxs)
  | RAodd (x, xxs) => RAeven (ralist_cons (P x0 x, xxs))

(* ****** ****** *)

implement ralist_head {a} (xs) = case+ xs of
  | RAone x => x
  | RAeven xxs => begin
      let val xx = ralist_head {P a a} xxs in xx.0 end
    end
  | RAodd (x, _) => x

implement ralist_head_exn (xs) = case+ xs of
  | RAnil () => $raise RandomAccessListSubscriptException
  | _ =>> ralist_head xs

(* ****** ****** *)

implement ralist_uncons {a} (xs) = case+ xs of
  | RAone x => (x, RAnil ())
  | RAeven xxs => let
      val (x01, xxs) = ralist_uncons {P a a} xxs
    in
      case+ xxs of
      | RAnil () => (x01.0, RAone x01.1)
      | _ =>> (x01.0, RAodd (x01.1, xxs))
    end
  | RAodd (x, xxs) => (x, RAeven xxs)

implement ralist_uncons_exn (xs) = case+ xs of
  | RAnil () => begin
      $raise RandomAccessListSubscriptException ()
    end
  | _ =>> ralist_uncons xs

(* ****** ****** *)

implement ralist_tail {a} (xs) = case+ xs of
  | RAone x => RAnil ()
  | RAeven xxs => let
      val (xx, xxs) = ralist_uncons {P a a} xxs
    in
      case+ xxs of
        | RAnil () => RAone xx.1 | _ =>> RAodd (xx.1, xxs)
    end
  | RAodd (_, xxs) => RAeven xxs

implement ralist_tail_exn (xs) = case+ xs of
  | RAnil () => begin
      $raise RandomAccessListSubscriptException ()
    end
  | _ =>> ralist_tail xs

(* ****** ****** *)

implement ralist_lookup {a} (xs, i) = case+ xs of
  | RAone x => x
  | RAeven xxs =>
    let val x01 = ralist_lookup {P a a} (xxs, nhalf i) in
       if i nmod 2 = 0 then x01.0 else x01.1
    end
  | RAodd (x, xxs) =>
    if i = 0 then x else let
      val x01 = ralist_lookup {P a a} (xxs, nhalf (i-1))
    in
      if i nmod 2 = 0 then x01.1 else x01.0
    end

implement ralist_lookup_exn (xs, i) =
  if i < ralist_length xs then ralist_lookup (xs, i)
  else begin
    $raise RandomAccessListSubscriptException ()
  end

(* ****** ****** *)

// Here is an example of constructing closures explicitly

dataviewtype closure_ (a: type) =
  {param: viewtype} CLOSURE_ (a) of (param, (param, a) -<fun> a)

// macro is fun!
macdef @ (c, x) = let val+ ~CLOSURE_ (p, f) = ,(c) in f (p, ,(x)) end

fun update {a:type} {n,i:nat | i < n} .<n>.
  (xs: ralist (a, n), i: int i, c: closure_ a):<> ralist (a, n) = begin
  case xs of
  | RAone x => RAone (c @ x)
  | RAeven xxs =>
    if i nmod 2 = 0 then let
      fn f (c: closure_ a, xx: P a a):<> P a a = '(c @ xx.0, xx.1)
    in
      RAeven (update {P a a} (xxs, nhalf i, CLOSURE_ (c, f)))
    end else let
      fn f (c: closure_ a, xx: P a a):<> P a a = '(xx.0, c @ xx.1)
    in
      RAeven (update {P a a} (xxs, nhalf i, CLOSURE_ (c, f)))
    end // end of [if]
  | RAodd (x, xxs) =>	      
    if i = 0 then RAodd (c @ x, xxs) else begin
      if i nmod 2 = 0 then let
        fn f (c: closure_ a, xx: P a a):<> P a a = '(xx.0, c @ xx.1)
      in
        RAodd (x, update {P a a} (xxs, nhalf (i-1), CLOSURE_ (c, f)))
      end else let
        fn f (c: closure_ a, xx: P a a):<> P a a = '(c @ xx.0, xx.1)
      in
        RAodd (x, update {P a a} (xxs, nhalf (i-1), CLOSURE_ (c, f)))
      end
    end // end of [if]
end // end of [update]

implement ralist_update (xs, i, x) =
  update (xs, i, CLOSURE_ (x, lam (x, _) => x))

implement ralist_update_exn (xs, i, x) =
  if i < ralist_length xs then begin
    update (xs, i, CLOSURE_ (x, lam (x, _) => x))
  end else begin
    $raise RandomAccessListSubscriptException ()
  end

(* ****** ****** *)

(* end of [ralist.dats] *)
