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

implement dynload_dummy () = () // loaded by [main_prelude]

(* ****** ****** *)

implement string_empty = "" // this requires dynamic loading

(* ****** ****** *)

implement string_concat (ss) = let
  val n0 = aux (ss, 0) where {
    fun aux {k:nat} .<k>.
      (ss: list (string, k), n: Nat):<> Nat = case+ ss of
      | list_cons (s, ss) => aux (ss, n + string0_length s)
      | list_nil () => n
  } // end of [where]
  fun loop1 {n0,i0,n,i:nat | i0 <= n0; i <= n} .<n0-i0>.
    (s0: string n0, n0: int n0, i0: int i0, s: string n, n: int n, i: int i)
    :<> [i0: nat | i0 <= n0] int i0 =
    if i < n then begin
      if i0 < n0 then (s0[i0] := s[i]; loop1 (s0, n0, i0+1, s, n, i+1)) else i0
    end else begin
      i0
    end // end of [loop1]
  fun loop2 {n0,i0,k:nat | i0 <= n0} .<k>.
    (s0: string n0, n0: int n0, i0: int i0, ss: list (string, k)):<> void =
    case+ ss of
    | list_cons (s, ss) => let
        val s = string1_of_string0 s
        val n = string1_length s
        val i0 = loop1 (s0, n0, i0, s, n, 0)
      in
        loop2 (s0, n0, i0, ss)
      end
    | list_nil () => ()
  val s0 = string_make_uninitialized n0
in
  loop2 (s0, n0, 0, ss); s0
end

(* ****** ****** *)

implement string1_explode (s) = let

fun loop {n,i:int | ~1 <= i; i < n} .<i+1>.
  (s: string n, i: int i, cs: list (char, n-i-1))
  :<> list (char, n) =
  if i >= 0 then loop (s, i-1, list_cons (s[i], cs)) else cs

in
  loop (s, length s - 1, list_nil ())
end // end of [string1_explode]

(* ****** ****** *)

%{

// a commonly used simple hash function

ats_uint_type atspre_string_hash_33 (ats_ptr_type s0)
{
  unsigned int hash_val ; unsigned char *s; int c;
  hash_val = 314159 ;

  s = (unsigned char*)s0 ;
  while (1) {
    c = *s ;
    if (!c) return hash_val ;
    hash_val = ((hash_val << 5) + hash_val) + c ;
    s += 1 ;
  }
}

%}

(* ****** ****** *)

(* end of [string.dats] *)
