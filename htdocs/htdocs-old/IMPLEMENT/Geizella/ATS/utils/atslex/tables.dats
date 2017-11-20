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

// July, 2007
// Author: Hongwei Xi (* hwxi AT cs DOT bu DOT edu *)

(* ****** ****** *)

staload "utils/atslex/lexing.sats"

//

staload "prelude/DATS/reference.dats"

//

dataviewtype tblopt =
  | {n:nat} {l:addr}
    tblopt_some of (array_v (int16, n, l) | ptr l, int n)
  | tblopt_none

extern fun new_tbloptref_some {n:nat} {l:addr}
  (pf: array_v (int16, n, l) | p: ptr l, n: int n): ref tblopt =
  "new_tbloptref_some"

implement new_tbloptref_some (pf | p, n) =
  ref_make_elt<tblopt> (tblopt_some (pf | p, n))

(* ****** ****** *)

extern fun table_ptr_free {a:viewt@ype}
  {n:nat} {l:addr} (pf: array_v (a, n, l) | p: ptr l):<> void
  = "table_ptr_free"

%{^

static inline
ats_void_type
table_ptr_free (ats_ptr_type p) { free (p) ; return ; }

%}

fn tbloptref_free (r_tblopt: ref tblopt): void = let
  val (vbox pf_tblopt | p_tblopt) = ref_get_view_ptr r_tblopt
in
  case+ !p_tblopt of
  | ~tblopt_some (pf | p, n) => begin
      table_ptr_free {int16} (pf | p); !p_tblopt := tblopt_none ()
    end
  | tblopt_none () => fold@ (!p_tblopt)
end // end of [tbloptref_free]
  
(* ****** ****** *)

assume accept_table_t = ref (tblopt)
assume transition_table_t = ref (tblopt)

//

extern fun __accept_table_make_fun
  (ntot: int, nfin: int, s: string): accept_table_t
  = "__accept_table_make_fun"

implement __accept_table_make ntot = lam nfin => lam s =>
  __accept_table_make_fun (ntot, nfin, s)

implement __accept_table_free (r_tblopt): void =
  tbloptref_free r_tblopt

//

implement accept_table_get (r_tblopt, nstate) = let
  var ans: int = (0: int)
  var err: int = (0: int)
  val () = let
    val (vbox pf_tblopt | p_tblopt) = ref_get_view_ptr r_tblopt
  in
    case+ !p_tblopt of
    | tblopt_none () => begin
        err := (1: int); fold@ (!p_tblopt)
      end // end of [tblopt_none]
    | tblopt_some (!pf | p, n) => let
        val nstate = int1_of_int nstate
      in
        if nstate < 0 then begin
          err := (2: int); fold@ (!p_tblopt)
        end else if nstate >= n then begin
          err := (3: int); fold@ (!p_tblopt)
        end else let
          prval pf_v = !pf
        in
          ans := int_of_int16 (!p.[nstate]);
          !pf := pf_v;
          fold@ (!p_tblopt)
        end
      end // end of [tblopt_some]
  end
in
  case+ err of
  | 1 => exit_errmsg (1, "lexing: accept_table_get: table is not available\n")
  | 2 => exit_errmsg (1, "lexing: accept_table_get: state number is illegal\n")
  | 3 => exit_errmsg (1, "lexing: accept_table_get: state number is illegal\n")
  | _ => ans
end

(* ****** ****** *)

#define NBITS_PER_BYTE 8
macdef NUMBER_OF_CHARS = (1 << NBITS_PER_BYTE - 1) + 1

extern fun
__transition_table_make_fun (n: int, s: string): transition_table_t =
  "__transition_table_make_fun"

implement __transition_table_make n = lam s =>
  __transition_table_make_fun (n, s)

implement __transition_table_free (r_tblopt): void =
  tbloptref_free r_tblopt

implement transition_table_get (r_tblopt, nstate, c) = let
(*
  val () = printf (
    "transition_table_get: nstate = %i and c = %i\n", @(nstate, int_of c)
  )
*)
  var ans: int = (0: int)
  var err: int = (0: int)
  val () = let
    val (vbox pf_tblopt | p_tblopt) = ref_get_view_ptr r_tblopt
  in
    case+ !p_tblopt of
      | tblopt_none () => begin
          err := (1: int); fold@ (!p_tblopt)
        end
      | tblopt_some (!pf | p, n) => let
          val i = int1_of_int
            ((nstate - 1) * NUMBER_OF_CHARS + (int_of c) + 1)
(*
          val () = $effmask_all begin
            printf ("transition_table_get: nstate = %i\n", @(nstate))
          end

          val () = $effmask_all begin
            printf ("transition_table_get: n = %i and i = %i\n", @(n,i))
          end
*)
        in
          if i < 0 then begin
            err := (2: int); fold@ (!p_tblopt)
          end else if i >= n then begin
            err := (3: int); fold@ (!p_tblopt)
          end else let
            prval pf_v = !pf
          in
            ans := int_of_int16 (!p.[i]);
            !pf := pf_v;
            fold@ (!p_tblopt)
          end
        end
  end
in
  case+ err of
    | 1 => exit_errmsg (1, "lexing: transition_table_get: table is not available\n")
    | 2 => exit_errmsg (1, "lexing: transition_table_get: state number is illegal\n")
    | 3 => exit_errmsg (1, "lexing: transition_table_get: state number is illegal\n")
    | _ => ans
end

(* ****** ****** *)

%{

#define NBITS_PER_BYTE 8
#define NUMBER_OF_CHARS ((1 << NBITS_PER_BYTE - 1) + 1)

ats_ptr_type
__accept_table_make_fun
  (ats_int_type ntot, ats_int_type nfin, ats_ptr_type s0) {
  int i, nstate, irule, sz ; ats_int16_type* p0 ;
  ats_uchar_type* s ; ats_ptr_type res ;

  // [calloc] is used as only integers are to be stored; thus,
  // there is no need to scan the allocated memory during GC;
  // the allocated memory is freed by a call to [free]
  sz = ntot+1 ; p0 = calloc (sz, sizeof(ats_int16_type)) ;  
  s = (ats_uchar_type*)s0;
  for (i = 0 ; i < nfin ; ++i) {
    nstate = (s[0] << NBITS_PER_BYTE) + s[1] ;
    s += 2 ;
    p0[nstate] = (s[0] << NBITS_PER_BYTE) + s[1] ;
    s += 2 ; 
/*
    fprintf (stdout, "%i -> %i\n", nstate, p0[nstate]) ;
*/
  }

  res = new_tbloptref_some (p0, sz) ;
/*
  fprintf (stdout, "__accept_table_make_fun: sz = %i\n", sz);
  fprintf (stdout, "__accept_table_make_fun: ptr = %p\n", p0);
  fprintf (stdout, "__accept_table_make_fun: res = %p\n", res);
*/
  return res ;
}

ats_ptr_type
__transition_table_make_fun (ats_int_type n, ats_ptr_type s0) {
  int i, j, c, sz;
  ats_int16_type *p0, *p ; ats_uchar_type *s ;
  ats_ptr_type res ;

  sz = n * NUMBER_OF_CHARS ;

  // [malloc] is used as only integers are to be stored; thus,
  // there is no need to scan the allocated memory during GC;
  // the allocated memory is freed by a call to [free]
  p0 = malloc (sz*sizeof(ats_int16_type)) ; p = p0 ;
  s = (ats_uchar_type*)s0;
  for (i = 0 ; i < n ; ++i) {
    for (j = 0 ; j < NUMBER_OF_CHARS ; ++j) {
      *p = (s[0] << NBITS_PER_BYTE) + s[1] ;
/*
      fprintf (stdout, "__transition_table_make_fun: %i: *p = %i\n", j, *p);
*/
      s += 2 ; ++p ;
    }
  }

  res = new_tbloptref_some (p0, sz) ;
/*
  fprintf (stdout, "__transition_table_make_fun: sz = %i\n", sz);
  fprintf (stdout, "__transition_table_make_fun: ptr = %p\n", p0);
  fprintf (stdout, "__transition_table_make_fun: res = %p\n", res);
*/
  return res ;
}

%}

(* ****** ****** *)

(* end of [tables.dats] *)
