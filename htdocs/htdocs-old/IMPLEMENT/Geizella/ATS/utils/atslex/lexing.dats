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

staload "utils/atslex/lexing.sats"

(* ****** ****** *)

assume position_t = '{ line= int, loff= int, toff= lint }

implement position_line (p) = p.line
implement position_loff (p) = p.loff
implement position_toff (p) = p.toff

implement lt_position_position (p1, p2) = p1.toff < p2.toff
implement lte_position_position (p1, p2) = p1.toff <= p2.toff
implement eq_position_position (p1, p2) = p1.toff = p2.toff
implement neq_position_position (p1, p2) = p1.toff <> p2.toff

extern fun position_make_int_int_lint
  (line: int, loff: int, toff: lint): position_t
  = "position_make_int_int_lint"

implement position_make_int_int_lint (line, loff, toff) =
  '{ line= line, loff= loff, toff= toff }

implement fprint_position (pf | fil, pos) =
  fprintf (pf | fil, "%li(line=%i, offs=%i)", @(pos.toff+1L, pos.line+1, pos.loff+1))

implement print_position (pos) = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
in
  fprint_position (file_mode_lte_w_w | !ptr_stdout, pos);
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_position]

implement prerr_position (pos) = let
  val (pf_stderr | ptr_stderr) = stderr_get ()
in
  fprint_position (file_mode_lte_w_w | !ptr_stderr, pos);
  stderr_view_set (pf_stderr | (*none*))
end // end of [prerr_position]

(* ****** ****** *)

typedef infile (v:view) = '{
  free= (v | (*none*)) -<cloref1> void
, getc= (!v | (*none*)) -<cloref1> int
}

assume infile_t = infile

//

implement infile_free (pf | infil) = infil.free (pf | (*none*))
implement infile_getc (pf | infil) = infil.getc (pf | (*none*))
(*
  let val c = infil.getc (pf | (*none*)) in
    printf ("infile_getc: c = %i\n", @(c)); c
  end
*)

//

implement infile_make_string (s) = let
  val [n:int] s = string1_of_string0 s
  val n = string1_length s
  typedef T = natLte n
  val [l:addr] (pf_gc, pf_at | p) = ptr_alloc_tsz {T} (sizeof<T>)
  viewdef V = @(free_gc_v l, T @ l)
  fn _free (pf: V | (*none*)):<cloref1> void = begin
     ptr_free {Nat} (pf.0, pf.1 | p)
  end // end of [_free]
  fn _getc (pf: !V | (*none*)):<cloref1> int = let
    prval pf_at: T @ l = pf.1
    val i = !p
    val ans: int = if i < n then (!p := i+1; int_of_char s[i]) else ~1
  in
    pf.1 := pf_at; ans
  end // end of [_getc]
in
  !p := 0; #[ V | (@(pf_gc, pf_at) | '{ free= _free, getc= _getc }) ]
end // end of [infile_make_string]

//

local

staload "libc/SATS/stdio.sats"

in

implement infile_make_file {m} {l} (pf_fil, pf_mod | fil) = let
  viewdef V = FILE m @ l
  fn _free (pf_fil: V | (*none*)):<cloref1> void = fclose (pf_fil | fil)
  fn _getc (pf_fil: !V | (*none*)):<cloref1> int = fgetc (pf_mod | !fil)
in
  #[ V | (pf_fil | '{ free= _free, getc= _getc }) ]
end // end of [infile_make_file]

implement infile_make_stdin () = let
  viewdef V = unit_v
  fn _free (pf: V | (*none*)):<cloref1> void = begin
     let prval unit_v () = pf in end
  end
  fn _getc (pf: !V | (*none*)):<cloref1> int = getchar ()
in
  #[ V | (unit_v () | '{ free= _free, getc= _getc } ) ]
end // end of [infile_make_stdin]

end // end of [local]

(* ****** ****** *)

implement lexing_engine_lexbuf (lxbf, transtbl, acctbl) = let

fun aux (lxbf: &lexbuf_t, irule: &int, nstate: int):<cloptr1> int =
  if nstate > 0 then let
    val irule_new = accept_table_get (acctbl, nstate)
(*
    val () = printf ("lexing_engine_lexbuf: aux: nstate = %i\n", @(nstate))
    val () = printf ("lexing_engine_lexbuf: aux: irule_new = %i\n", @(irule))
*)
    val () =
      if irule_new > 0 then begin
        lexbuf_lstpos_set (lxbf); irule := irule_new
      end
    val c = lexbuf_char_next (lxbf)
(*
    val () = begin
      printf ("lexing_engine_lexbuf: c = %c and c = %i\n", @(c, int_of c))
    end
*)
    val nstate = transition_table_get (transtbl, nstate, c)
(*
    val () = printf ("lexing_engine_lexbuf: nstate = %i\n", @(nstate))
*)
  in
    aux (lxbf, irule, nstate)
  end else begin
    lexbuf_curpos_set (lxbf);
(*
    printf ("lexing_engine_lexbuf: end: irule = %i\n", @(irule));
*)
    irule
  end

var irule = (0: int)

in

  lexbuf_fstpos_set (lxbf); aux (lxbf, irule, 1)

end // end of [lexing_engine_lexbuf]


implement lexing_engine (transtbl, acctbl) = let
  val (pf_lexbuf | lexbuf) = lexing_lexbuf_get ()
  val irule = lexing_engine_lexbuf (!lexbuf, transtbl, acctbl)
in
  lexing_lexbuf_set (pf_lexbuf | lexbuf); irule
end // end of [lexing_engine]

(* ****** ****** *)

implement lexeme_get (i) = let
  val (pf_lexbuf | lexbuf) = lexing_lexbuf_get ()
  val c = lexeme_get_lexbuf (!lexbuf, i)
in
  lexing_lexbuf_set (pf_lexbuf | lexbuf); c
end // end of [lexeme_get]

implement lexeme_set (i, c) = let
  val (pf_lexbuf | lexbuf) = lexing_lexbuf_get ()
  val () = lexeme_set_lexbuf (!lexbuf, i, c)
in
  lexing_lexbuf_set (pf_lexbuf | lexbuf)
end // end of [lexeme_set]

implement lexeme_string () = let
  val (pf_lexbuf | lexbuf) = lexing_lexbuf_get ()
  val s = lexeme_string_lexbuf (!lexbuf)
in
  lexing_lexbuf_set (pf_lexbuf | lexbuf); s
end // end of [lexeme_string]

implement lexeme_lint (base) = let
  val (pf_lexbuf | lexbuf) = lexing_lexbuf_get ()
  val li = lexeme_lint_lexbuf (!lexbuf, base)
in
  lexing_lexbuf_set (pf_lexbuf | lexbuf); li
end // end of [lexeme_lint]

implement lexeme_int (base) = int_of_lint (lexeme_lint base)

implement lexing_is_eof () = let
  val (pf_lexbuf | lexbuf) = lexing_lexbuf_get ()
  val b = lexbuf_is_eof (!lexbuf)
in
  lexing_lexbuf_set (pf_lexbuf | lexbuf); b
end // end of [lexing_is_of]

(* ****** ****** *)

implement lexing_error () = $raise LexingErrorException

(* ****** ****** *)

extern fun lexing_lexbuf_markroot (): void = "lexing_lexbuf_markroot"

val () = let // initialization
  val () = lexing_lexbuf_markroot ()
in
  // empty
end

(* ****** ****** *)

%{^

#include "libc/CATS/stdio.cats"

%}

%{

typedef struct {
  char* buf_ptr ;
  int buf_size ;
  ats_ptr_type infile ;
  int fstpos ;
  int fstpos_line ; // line number
  int fstpos_loff ; // line offset
  long int fstpos_toff ; // total offset
  int lstpos ;
  int lstpos_line ; // line number
  int lstpos_loff ; // line offset
  long int lstpos_toff ; // total offset
  int curpos ;
  int curpos_line ; // line number
  int curpos_loff ; // line offset
  long int curpos_toff ; // total offset
  int endpos ;
} lexbuf ;

//

ats_ptr_type
lexbuf_fstpos_get (ats_ptr_type lxbf0) {
  lexbuf *lxbf = (lexbuf *)lxbf0 ;
  return position_make_int_int_lint
    (lxbf->fstpos_line, lxbf->fstpos_loff, lxbf->fstpos_toff) ;
}

ats_void_type
lexbuf_fstpos_set (ats_ptr_type lxbf0) {
  lexbuf *lxbf = (lexbuf *)lxbf0 ;
  lxbf->fstpos = lxbf->curpos ;
  lxbf->fstpos_line = lxbf->curpos_line ;
  lxbf->fstpos_loff = lxbf->curpos_loff ;
  lxbf->fstpos_toff = lxbf->curpos_toff ;
  return ;
}

//

ats_ptr_type
lexbuf_lstpos_get (ats_ptr_type lxbf0) {
  lexbuf *lxbf = (lexbuf *)lxbf0 ;
  return position_make_int_int_lint
    (lxbf->lstpos_line, lxbf->lstpos_loff, lxbf->lstpos_toff) ;
}

ats_void_type
lexbuf_lstpos_set (ats_ptr_type lxbf0) {
  lexbuf *lxbf = (lexbuf *)lxbf0 ;
  lxbf->lstpos = lxbf->curpos ;
  lxbf->lstpos_line = lxbf->curpos_line ;
  lxbf->lstpos_loff = lxbf->curpos_loff ;
  lxbf->lstpos_toff = lxbf->curpos_toff ;
  return ;
}

//

ats_ptr_type
lexbuf_curpos_get (ats_ptr_type lxbf0) {
  lexbuf *lxbf = (lexbuf *)lxbf0 ;
  return position_make_int_int_lint
    (lxbf->curpos_line, lxbf->curpos_loff, lxbf->curpos_toff) ;
}

ats_void_type
lexbuf_curpos_set (ats_ptr_type lxbf0) {
  lexbuf *lxbf = (lexbuf *)lxbf0 ;
  lxbf->curpos = lxbf->lstpos ;
  lxbf->curpos_line = lxbf->lstpos_line ;
  lxbf->curpos_loff = lxbf->lstpos_loff ;
  lxbf->curpos_toff = lxbf->lstpos_toff ;
  return ;
}

//

ats_int_type
lexbuf_size_get (ats_ptr_type lxbf0) {
  int sz ; lexbuf *lxbf ;
  lxbf = (lexbuf *)lxbf0;
  sz = lxbf->lstpos - lxbf->fstpos ;
  if (sz < 0) { sz += lxbf->buf_size ; }
  return sz ;
}

/* ****** ****** */

#define BUF_SIZE 1024
#define BUF_RESIZE 256

/* ****** ****** */

ats_void_type
lexbuf_resize (lexbuf *lxbf) {
  int fstpos, curpos, lstpos, endpos ;
  int buf_size, buf_size_new ;
  char *buf_ptr, *buf_ptr_new;
/*
  fprintf (stdout, "lexbuf_resize: before: buf_size = %i\n", lxbf->buf_size) ;
  fprintf (stdout, "lexbuf_resize: before: fstpos = %i\n", lxbf->fstpos) ;
  fprintf (stdout, "lexbuf_resize: before: curpos = %i\n", lxbf->curpos) ;
  fprintf (stdout, "lexbuf_resize: before: lstpos = %i\n", lxbf->lstpos) ;
  fprintf (stdout, "lexbuf_resize: before: endpos = %i\n", lxbf->endpos) ;
*/
  buf_ptr = lxbf->buf_ptr ;
  buf_size = lxbf->buf_size ;
  fstpos = lxbf->fstpos ;
  endpos = lxbf->endpos ;

  buf_size_new = buf_size + buf_size ;
  buf_ptr_new = ats_malloc_gc(buf_size_new) ;

  lxbf->buf_ptr = buf_ptr_new ;
  lxbf->buf_size = buf_size_new ;

  lxbf->fstpos = 0 ;

  if (fstpos <= endpos) {
    memcpy(buf_ptr_new, buf_ptr+fstpos, endpos-fstpos) ;
    lxbf->endpos = endpos - fstpos ;
  } else {
    memcpy(buf_ptr_new, buf_ptr+fstpos, buf_size-fstpos) ;
    memcpy(buf_ptr_new+buf_size-fstpos, buf_ptr, endpos) ;
    lxbf->endpos = buf_size + endpos - fstpos ;
  }

  curpos = lxbf->curpos ;

  if (fstpos <= curpos) {
    lxbf->curpos = curpos - fstpos ;
  } else {
    lxbf->curpos = buf_size + curpos - fstpos ;
  }

  lstpos = lxbf->lstpos ;

  if (fstpos <= lstpos) {
    lxbf->lstpos = lstpos - fstpos ;
  } else {
    lxbf->lstpos = buf_size + lstpos - fstpos ;
  }

/*
  fprintf (stdout, "lexbuf_resize: after: buf_size = %i\n", lxbf->buf_size) ;
  fprintf (stdout, "lexbuf_resize: after: fstpos = %i\n", lxbf->fstpos) ;
  fprintf (stdout, "lexbuf_resize: after: curpos = %i\n", lxbf->curpos) ;
  fprintf (stdout, "lexbuf_resize: after: lstpos = %i\n", lxbf->lstpos) ;
  fprintf (stdout, "lexbuf_resize: after: endpos = %i\n", lxbf->endpos) ;
*/

  ats_free_gc(buf_ptr) ;
}

ats_void_type
lexbuf_resize_if (lexbuf *lxbf) {
  int fstpos, endpos ;

/*
  fprintf (stdout, "lexbuf_resize_if: buf_size = %i\n", lxbf->buf_size) ;
  fprintf (stdout, "lexbuf_resize_if: fstpos = %i\n", lxbf->fstpos) ;
  fprintf (stdout, "lexbuf_resize_if: curpos = %i\n", lxbf->curpos) ;
  fprintf (stdout, "lexbuf_resize_if: lstpos = %i\n", lxbf->lstpos) ;
  fprintf (stdout, "lexbuf_resize_if: endpos = %i\n", lxbf->endpos) ;
*/

  fstpos = lxbf->fstpos ;
  endpos = lxbf->endpos ;

  if (fstpos <= endpos) {
    if (endpos - fstpos + BUF_RESIZE > lxbf->buf_size) {
      lexbuf_resize(lxbf) ;
    }
  } else {
    if (endpos + BUF_RESIZE >= fstpos) {
      lexbuf_resize (lxbf) ;
    }
  }
  return ;
}

ats_char_type
lexbuf_refill (ats_ptr_type lxbf0) {
  lexbuf *lxbf ;
  char c, *buf_ptr ;
  int fstpos, curpos, endpos ;

  lxbf = (lexbuf*)lxbf0 ;

  lexbuf_resize_if (lxbf) ;

  buf_ptr = lxbf->buf_ptr ;
  fstpos = lxbf->fstpos ;
  endpos = lxbf->endpos ;
/*
  fprintf (stdout, "lexbuf_refill: fstpos = %i\n", fstpos) ;
  fprintf (stdout, "lexbuf_refill: endpos = %i\n", endpos) ;
*/
  if (fstpos <= endpos) {
    while (endpos+1 < lxbf->buf_size) {
      c = lexing_infile_getc(lxbf->infile) ;
      if (c < 0) { lxbf->endpos = endpos ; return ; }
      buf_ptr[endpos] = c; ++endpos ;
    }

    if (fstpos == 0) { lxbf->endpos = endpos ; return ; }

    c = lexing_infile_getc(lxbf->infile) ;
    if (c < 0) { lxbf->endpos = endpos ; return ; }
    buf_ptr[endpos] = c; endpos = 0;

  }

  while (endpos+1 < fstpos) {
    c = lexing_infile_getc(lxbf->infile) ;
    if (c < 0) { lxbf->endpos = endpos ; return ; }
    buf_ptr[endpos] = c; ++endpos ;
  }

  lxbf->endpos = endpos ;
  return ;
}

ats_void_type
lexbuf_curpos_next (lexbuf *lxbf, char c) {
  int curpos1 = lxbf->curpos + 1 ;

  if (curpos1 < lxbf->buf_size) {
    lxbf->curpos = curpos1;
  } else {
    lxbf->curpos = 0;
  }

  if (c == '\n') {
    lxbf->curpos_line += 1; lxbf->curpos_loff = 0; lxbf->curpos_toff += 1 ;
  } else {
    lxbf->curpos_loff += 1 ; lxbf->curpos_toff += 1 ;
  }
  return ;
}

ats_char_type
lexbuf_char_next (ats_ptr_type lxbf0) {
  lexbuf *lxbf ;
  char c, *buf_ptr ;
  int fstpos, curpos, endpos ;

  lxbf = (lexbuf*)lxbf0 ;

  buf_ptr = lxbf->buf_ptr ;
  curpos = lxbf->curpos ;
  endpos = lxbf->endpos ;

  if (curpos != endpos) {
    c = buf_ptr[curpos] ; lexbuf_curpos_next (lxbf, c); return c ;
  }

  lexbuf_refill (lxbf0) ;

  buf_ptr = lxbf->buf_ptr ;
  curpos = lxbf->curpos ;
  endpos = lxbf->endpos ;
/*
  fprintf (stdout, "lexbuf_char_next: refill: curpos = %i\n", curpos);
  fprintf (stdout, "lexbuf_char_next: refill: endpos = %i\n", endpos);
*/
  if (curpos != endpos) {
    c = buf_ptr[curpos] ; lexbuf_curpos_next (lxbf, c); return c ;
  }

  return -1 ;
}

ats_bool_type
lexbuf_is_eof (ats_ptr_type lxbf0) {
  lexbuf *lxbf = (lexbuf*)lxbf0 ;

  if (lxbf->curpos != lxbf->endpos) return ats_false_bool ;

  lexbuf_refill (lxbf0) ;  

  if (lxbf->curpos != lxbf->endpos) {
    return ats_false_bool ;
  } else {
    return ats_true_bool ;
  }
}

/* ****** ****** */

ats_ptr_type
lexing_fstpos_get () {
  ats_ptr_type pos ; lexbuf *lxbf ;
  lxbf = (lexbuf *)(lexing_lexbuf_get()) ;
  pos = lexbuf_fstpos_get (lxbf) ;
  lexing_lexbuf_set(lxbf) ;
  return pos;
}

ats_ptr_type
lexing_lstpos_get () {
  ats_ptr_type pos ; lexbuf *lxbf ;
  lxbf = (lexbuf *)(lexing_lexbuf_get()) ;
  pos = lexbuf_lstpos_get (lxbf) ;
  lexing_lexbuf_set(lxbf) ;
  return pos;
}

ats_ptr_type
lexing_curpos_get () {
  ats_ptr_type pos ; lexbuf *lxbf ;
  lxbf = (lexbuf *)(lexing_lexbuf_get()) ;
  pos = lexbuf_curpos_get (lxbf) ;
  lexing_lexbuf_set(lxbf) ;
  return pos;
}

/* ****** ****** */

ats_void_type
lexbuf_curpos_fprint (ats_ptr_type fil, lexbuf *lxbf) {
  fprintf ((FILE *)fil, "%i(line=%i, offset=%i)",
    lxbf->curpos_toff+1, lxbf->curpos_line+1, lxbf->curpos_loff+1
  ) ;
  return ;
}

ats_void_type
lexing_curpos_prerr () {
  lexbuf *lxbf ;
  lxbf = (lexbuf *)(lexing_lexbuf_get()) ;
  lexbuf_curpos_fprint (stderr, lxbf) ;
  lexing_lexbuf_set(lxbf) ;
  return ;
}

/* ****** ****** */

ats_ptr_type
lexbuf_make_infile(const ats_ptr_type infile) {
  char *buf_ptr ; lexbuf *lxbf ;

  buf_ptr = ats_malloc_gc(BUF_SIZE) ;
  lxbf = ats_malloc_gc(sizeof(lexbuf)) ;
  lxbf->buf_ptr = buf_ptr ;
  lxbf->buf_size = BUF_SIZE ;
  lxbf->infile = infile ;

  lxbf->fstpos = 0 ;
  lxbf->fstpos_line = 0 ;
  lxbf->fstpos_loff = 0 ;
  lxbf->fstpos_toff = 0 ;

  lxbf->lstpos = 0 ;
  lxbf->lstpos_line = 0 ;
  lxbf->lstpos_loff = 0 ;
  lxbf->lstpos_toff = 0 ;

  lxbf->curpos = 0 ;
  lxbf->curpos_line = 0 ;
  lxbf->curpos_loff = 0 ;
  lxbf->curpos_toff = 0 ;

  lxbf->endpos = 0 ;
/*
  printf ("lexbuf_make_infile: lxbf = %p\n", lxbf) ;
*/
  return lxbf ;
}

ats_char_type
lexbuf_free (ats_ptr_type lxbf0) {
  lexbuf *lxbf ;
  lxbf = (lexbuf*)lxbf0 ;

  lexing_infile_free (lxbf->infile) ;
  ats_free_gc (lxbf->buf_ptr) ;
  return ;
}

/* ****** ****** */

ats_char_type
lexeme_get_lexbuf (ats_ptr_type lxbf0, ats_int_type i) {
  int len, fstpos, lstpos, bufsz ;
  lexbuf *lxbf ;

  if (i < 0) {
    ats_exit_errmsg (
      1, "lexeme_get_lexbuf: index is out_of_bounds.\n"
    ) ;
  }

  lxbf = (lexbuf*)lxbf0 ;

  fstpos = lxbf->fstpos ;
  lstpos = lxbf->lstpos ;
  len = lstpos - fstpos ;
  bufsz = lxbf->buf_size ;
  if (len < 0) { len += bufsz ; }

  if (i > len) {
    ats_exit_errmsg (
      1, "lexeme_get_lexbuf: index is out_of_bounds.\n"
    ) ;
  }

  i = fstpos + i ;
  if (i >= bufsz) { i -= bufsz ; }

  return *((lxbf->buf_ptr) + i) ;
}

ats_void_type lexeme_set_lexbuf
  (ats_ptr_type lxbf0, ats_int_type i, ats_char_type c) {
  int len, fstpos, lstpos, bufsz ;
  lexbuf *lxbf ;

  if (i < 0) {
    ats_exit_errmsg (
      1, "lexeme_set_lexbuf: index is out_of_bounds.\n"
    ) ;
  }

  lxbf = (lexbuf*)lxbf0 ;

  fstpos = lxbf->fstpos ;
  lstpos = lxbf->lstpos ;
  len = lstpos - fstpos ;
  bufsz = lxbf->buf_size ;
  if (len < 0) { len += bufsz ; }

  if (i > len) {
    ats_exit_errmsg (
      1, "lexeme_set_lexbuf: index is out_of_bounds.\n"
    ) ;
  }

  i = fstpos + i ;
  if (i >= bufsz) { i -= bufsz ; }

  *((lxbf->buf_ptr) + i) = c ;

  return ;
}

/* ****** ****** */

ats_ptr_type
lexeme_string_lexbuf (ats_ptr_type lxbf0) {
  int len, fstpos, lstpos ;
  char *src, *dst0, *dst ;
  lexbuf *lxbf ;

  lxbf = (lexbuf*)lxbf0 ;

  fstpos = lxbf->fstpos ;
  lstpos = lxbf->lstpos ;
  len = lstpos - fstpos ;
  if (len < 0) { len += lxbf->buf_size ; }

  src = (lxbf->buf_ptr) + fstpos ;
  dst0 = ats_malloc_gc ((len + 1) * sizeof(char)) ;
  dst = dst0 ;

  if (lstpos < fstpos) {
    while (fstpos < lxbf->buf_size) {
      *dst = *src ; ++fstpos ; ++src ; ++dst ;
    }
    fstpos = 0 ; src = lxbf->buf_ptr ;
  }

  while (fstpos < lstpos) {
    *dst = *src ; ++fstpos ; ++src ; ++dst ;
  }

  *dst = '\000' ;

  return dst0 ;
}

/* ****** ****** */

ats_lint_type
lexeme_lint_lexbuf (ats_ptr_type lxbf0, ats_int_type base) {
  int fstpos ;
  char *src ;
  lexbuf *lxbf ;

  lxbf = (lexbuf*)lxbf0 ;

  fstpos = lxbf->fstpos ;
  return strtol ((lxbf->buf_ptr) + fstpos, (char **)0, base) ;
}

/* ****** ****** */

static ats_ptr_type the_lexbuf = (lexbuf*)0 ;

ats_void_type lexing_lexbuf_markroot () {
  ats_gc_markroot (&the_lexbuf, sizeof(ats_ptr_type)) ;
  return ;
}

static ats_int_type the_lexbuf_flag = 0 ;

ats_ptr_type lexing_lexbuf_get() {
  if (the_lexbuf_flag == 0) {
    ats_exit_errmsg (
      1, "[lexeme_get] failed: The default lexbuf is not set!\n"
    );
  }
  the_lexbuf_flag = 0 ;
  return the_lexbuf ;
}

ats_void_type
lexing_lexbuf_set(ats_ptr_type lxbf) {
  if (the_lexbuf_flag == 1) {
    ats_exit_errmsg (
      1, "[lexeme_set] failed: The default lexbuf is already set!\n"
    );
  }
  the_lexbuf_flag = 1 ;
  the_lexbuf = lxbf ;
/*
  printf ("lexing_lexbuf_set: lxbf = %p\n", lxbf) ;
*/
  return ;
}

ats_void_type lexing_lexbuf_free() {
  lexbuf_free (lexing_lexbuf_get()) ;
  return ;
}

%}

(* ****** ****** *)

(* end of [lexing.dats] *)
