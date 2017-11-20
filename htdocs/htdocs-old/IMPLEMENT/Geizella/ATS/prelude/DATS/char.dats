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

//// implemented in char.cats

#define c2i int_of_char
#define i2c char_of_int

(* ****** ****** *)

implement eq_char_char (c1, c2) = c2i c1 = c2i c2
implement neq_char_char (c1, c2) = c2i c1 <> c2i c2

implement lt_char_char (c1, c2) = c2i c1 < c2i c2
implement lte_char_char (c1, c2) = c2i c1 <= c2i c2
implement gt_char_char (c1, c2) = c2i c1 > c2i c2
implement gte_char_char (c1, c2) = c2i c1 >= c2i c2

implement compare_char_char (c1, c2) = compare (c2i c1, c2i c2)

(* ****** ****** *)

implement char_isalpha c = char_islower c || char_isupper c

implement char_isalnum c = char_isalpha c || char_isdigit c

implement char_isascii c = let val i = c2i c in 0 <= i && i < 128 end

implement char_iscntrl c =
  let val i = c2i c in (0 <= i && i < 32) || (i = 127) end

implement char_isdigit c = '0' <= c && c <= '9'

implement char_isgraph c = let val i = c2i c in 32 < i && i < 127 end

implement char_islower c = 'a' <= c && c <= 'z'

implement char_isnull c = c2i c = 0

implement char_isprint c = let val i = c2i c in 32 <= i && i < 127 end

implement char_ispunct c =
  char_isprint c && ~(char_isalnum c) && ~(char_isspace c)

implement char_isspace c = 
  (c = ' ' || c = '\f' || c = '\n' || c = '\r' || c = '\t' || c = '\v')

implement char_isupper c = 'A' <= c && c <= 'Z'

implement char_isxdigit c =
  char_isdigit c || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')

implement char_tolower c =
  if char_isupper c then i2c (c2i c - c2i 'A' + c2i 'a') else c

implement char_toupper c =
  if char_islower c then i2c (c2i c - c2i 'a' + c2i 'A') else c

implement char_tostring c = string_make_with_char (1, c)
