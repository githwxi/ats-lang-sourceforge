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

staload "libc/SATS/stdio.sats"
staload "libc/SATS/unistd.sats"

(* ****** ****** *)

staload "basics.sats"
staload "atscc.sats"
staload "atslib.sats"

(* ****** ****** *)

extern
fun gcc_libfile_exec (infile: string, outfile: string): void
  = "gcc_libfile_exec"

implement gcc_libfile_err (infile, outfile) = let
  fn cmd ():<cloptr1> void = gcc_libfile_exec (infile, outfile)
in
  fork_and_exec_and_wait (cmd)
end

extern
fun ar_r_exec (libfile: string, objfile: string): void
  = "ar_r_exec"

// archive with replacement
implement ar_r_err (libfile, objfile) =
  fork_and_exec_and_wait (lam () => ar_r_exec (libfile, objfile))

(* ****** ****** *)

#define i2u uint_of_int

fn char_identifize (c: char):<cloptr1> String =
  if char_isalnum c then tostring c
  else begin
    let
       val i = uint_of_char c
       val c1 = i / i2u 16 and c2 = i mod i2u 16
    in
       tostringf_size (4, "_%x%x", @(c1, c2))
    end
  end

implement ccomp_gcc_ar_libfile (infile, libfile) =
  let
     val sfx = suffix_of_filename infile
     val flag: int =
        if stropt_is_none sfx then
          exit_prerrf {int} (
            1, "Exit: %s: no suffix\n.", @(infile)
          )
        else begin case stropt_unsome sfx of
          | "sats" => 0
          | "dats" => 1
          | _ => exit_prerrf {int} (
              1, "Exit: %s: unsupported suffix\n.", @(infile)
            )
        end
     val infull: string =
       if filename_is_local infile then
         tostringf_size (64, "%s/%s", @(getcwd (), infile))
       else infile
     val outbase = string_trans (infull, char_identifize)
     val outfile = atslib_output_global + outbase
     val outfile_c = outfile + ".c"
     val status = ccomp_file_to_file_err (flag, infile, outfile_c)
     val () = 
       if (status <> 0) then exit_prerrf {void}
         (status, "Exit: [ccomp_gcc_ar_libfile(%s)] failed: ccomp\n", @(infile))
       else ()
     val outfile_o = outfile + ".o"
     val status = gcc_libfile_err (outfile_c, outfile_o)
     val () =
       if (status <> 0) then exit_prerrf {void}
         (status, "Exit: [ccomp_gcc_ar_libfile(%s)] failed: gcc\n", @(infile))
       else ()
     val status = ar_r_err (libfile, outfile_o)
     val () =
       if (status <> 0) then exit_prerrf {void}
         (status, "Exit: [ccomp_gcc_ar_libfile(%s)] failed: ar\n", @(infile))
  in
     printf ("The file [%s] has been compiled and archived.\n", @(infile))
  end

(* ****** ****** *)

extern fun fget_line {m:fm}
  (pf: file_mode_lte (m, r) | f: &FILE m): String
  = "fget_line"

fun library_make_loop {m:fm} {l_file:addr}
  (file: &FILE r, dir: String, libfilename: string): void =
  if feof (file) <> 0 then ()
  else begin
    let
       val filename = fget_line (file_mode_lte_r_r | file)
    in
       if string1_is_not_empty filename then
         ccomp_gcc_ar_libfile (dir + filename, libfilename) ;
       library_make_loop (file, dir, libfilename)
    end
  end

(* ****** ****** *)

implement libcats_make () =
  let
     val libcats_txt = ATSHOME_append ".libcats"
     val (pf_file | p_file) = fopen (libcats_txt, #mode="r")
  in
     library_make_loop (!p_file, ATSHOME, libcats_global);
     fclose (pf_file | p_file)
  end

// implement libcats_mt_make () = library_make (libcats_mt_global)

(* ****** ****** *)

implement libatslex_make () =
  let
     val dir = ATSHOME_append "utils/atslex/"
  in
     ccomp_gcc_ar_libfile (dir + "lexing.sats", libatslex_global) ;
     ccomp_gcc_ar_libfile (dir + "lexing.dats", libatslex_global) ;
     ccomp_gcc_ar_libfile (dir + "tables.dats", libatslex_global) ;
  end

(* ****** ****** *)

%{^

#include <unistd.h>

#include "libc/CATS/stdio.cats"

typedef ats_ptr_type ats_string_type ;

extern ats_string_type ATSHOME ;
extern ats_string_type runtime_global ;

ats_void_type
gcc_libfile_exec
  (ats_string_type input_c, ats_string_type output_o) {
  execlp(
    "gcc", "gcc",
    "-I", runtime_global, "-I", ATSHOME, "-O3",
    "-o", output_o, "-c", input_c, (char *)0
  ) ;
  return ;
}

ats_void_type
ar_r_exec (ats_string_type lib, ats_string_type output_o) {
  execlp("ar", "ar", "-r", lib, output_o, (char *)0) ;
  return ;
}

#define INCSZ 1024

ats_string_type fget_line (ats_ptr_type file) {
  int c;
  int i, sz;
  char *buf0, *buf1, *p;

  if (feof((FILE *)file)) {
    ats_exit_errmsg(1, (ats_string_type)"Exit: [fget_line] failed: EOF\n");
  }

  sz = INCSZ;
  buf0 = (char *)ats_malloc_gc(sz); p = buf0;

  while (1) {
    for (i = 0; i < INCSZ; ++i) {
      c = fgetc ((FILE *)file) ;
      if (c == '\n' || c == EOF) { *p = '\000'; return buf0; }
      *p = c; ++p;
    }
    buf1 = (char *)ats_malloc_gc (sz + INCSZ) ;
    memcpy (buf1, buf0, sz) ;
    ats_free_gc (buf0) ;    
    buf0 = buf1 ; p = buf0 + sz;
    sz = sz + INCSZ ;
  }

  return (char *)0 ; /* deadcode */
}

%}

(* ****** ****** *)

(* end of [atslib.dats] *)
