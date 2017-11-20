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
 * along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
 * Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "top.sats"

(* ****** ****** *)

datatype chars =
  | chars_nil | chars_cons of (char, char, chars)

assume charset_t = chars

#define nil chars_nil
#define cons chars_cons

//

implement fprint_charset {m:file_mode} (pf_mod | fil, cs): void =
  let
    fun loop (fil: &FILE m, cs: chars) =
      case+ cs of
        | cons (c1, c2, cs) =>
          if c1 = c2 then begin
            fprintf (pf_mod | fil, " '%c'", @(c1)); loop (fil, cs)
          end else begin
            fprintf (pf_mod | fil, " '%c'-'%c'", @(c1, c2)); loop (fil, cs)
          end
        | nil () => ()
  in
    case+ cs of
      | cons (c1, c2, cs) =>
          if c1 = c2 then begin
            fprintf (pf_mod | fil, "[ '%c'", @(c1));
            loop (fil, cs);
            fprint_string (pf_mod | fil, " ]")
          end else begin
            fprintf (pf_mod | fil, "[ '%c'-'%c'", @(c1, c2));
            loop (fil, cs);
            fprint_string (pf_mod | fil, " ]")
          end
      | nil () => fprint_string (pf_mod | fil, "[]")
  end

implement print_charset (cs) =
  let
     val (pf_stdout | ptr_stdout) = stdout_get ()
  in
     fprint_charset (file_mode_lte_w_w | !ptr_stdout, cs);
     stdout_view_set (pf_stdout | (*none*))
  end

implement prerr_charset (cs) =
  let
     val (pf_stderr | ptr_stderr) = stderr_get ()
  in
     fprint_charset (file_mode_lte_w_w | !ptr_stderr, cs);
     stderr_view_set (pf_stderr | (*none*))
  end

(* ****** ****** *)

//

implement charset_nil = nil ()
implement charset_all = cons ('\000', '\177', nil ())
implement charset_eof = cons ('\200', '\377', nil ())

//

implement charset_interval (c1, c2) =
  if c1 <= c2 then cons (c1, c2, nil ()) else cons (c2, c1, nil ())

implement charset_singleton c = cons (c, c, nil ())

//

implement charset_complement (cs) =
  charset_difference (charset_all, cs)

//

implement charset_is_member (cs, c0) = let

fun loop (cs: chars, c0: char): bool = case+ cs of
  | cons (c1, c2, cs) => begin
      if c1 <= c0 then
        (if c0 <= c2 then true else loop (cs, c0))
      else loop (cs, c0)
    end
  | nil () => false

in

  loop (cs, c0)

end // end of charset_is_member

//

implement charset_union (cs1, cs2) = let

fun loop (cs1: chars, cs2: chars): chars =
  case+ (cs1, cs2) of
    | (nil (), _) => cs2
    | (_, nil ()) => cs1
    | (cons (c11, c12, cs10), cons (c21, c22, cs20)) =>
      if c21 < c11 then begin
        loop (cs2, cs1)
      end else if 1 < c21 - c12 then begin
        cons (c11, c12, loop (cs10, cs2))
      end else if c12 <= c22 then begin
        loop (cons (c11, c22, cs20), cs10)
      end else begin
        loop (cs1, cs20)
      end
in

loop (cs1, cs2)

end

//

implement charset_intersect (cs1, cs2) = let

fun loop (cs1: chars, cs2: chars): chars =
  case+ (cs1, cs2) of
    | (nil (), _) => nil ()
    | (_, nil ()) => nil ()
    | (cons (c11, c12, cs10), cons (c21, c22, cs20)) =>
      if c21 < c11 then begin
        loop (cs2, cs1)
      end else if c12 < c21 then begin
        loop (cs10, cs2)
      end else if c12 <= c22 then begin
        cons (c21, c12, loop (cs10, cs2))
      end else begin
        cons (c21, c22, loop (cs1, cs20))
      end
in

loop (cs1, cs2)

end

//

implement add_char_int (c, i) =
  char_of_int (int_of_char c + i)

implement sub_char_int (c, i) =
  char_of_int (int_of_char c - i)

//

implement charset_difference (cs1, cs2) = let

fun loop (cs1: chars, cs2: chars): chars =
  case+ (cs1, cs2) of
    | (nil (), _) => nil ()
    | (_, nil ()) => cs1
    | (cons (c11, c12, cs10), cons (c21, c22, cs20)) =>
      if c12 < c21 then begin
        loop (cs10, cs2)
      end else if c22 < c11 then begin
        loop (cs1, cs20)
      end else if c12 <= c22 then begin
        if c11 < c21 then begin
          cons (c11, c21-1, loop (cs10, cs2))
        end else begin
          loop (cs10, cs2)
        end
      end else begin // c22 < c12
        if c11 < c21 then begin
          cons (c11, c21-1, loop (cons (c22+1, c12, cs10), cs20))
        end else begin
          loop (cons (c22+1, c12, cs10), cs20)
        end
      end
in
   loop (cs1, cs2)
end

(* ****** ****** *)

(* end of [charset.dats] *)
