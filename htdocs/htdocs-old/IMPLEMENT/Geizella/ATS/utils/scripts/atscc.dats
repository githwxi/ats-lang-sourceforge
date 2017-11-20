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

staload "libc/SATS/unistd.sats"

(* ****** ****** *)

staload "basics.sats"
staload "atscc.sats"

(* ****** ****** *)

val () = assert_prerrf (
  file_is_exec atsopt_global,
  "The file [%s] is not executable.\n",
  @(atsopt_global)
)

fn print_usage_of_ccomp_file (): void =
  print ("Usage: ccomp_file [infile] -output=[outfile]\n")

(* ****** ****** *)

extern fun typecheck_file_exec (i: int, s: string): void
  = "typecheck_file_exec"

implement typecheck_file (flag, infile) = let
  fn cmd ():<cloptr1> void = typecheck_file_exec (flag, infile)
  val status = fork_and_exec_and_wait (cmd)
in
  if (status <> 0) then exit_prerrf {void}
    (status, "Exit: [typecheck_file(%s)] failed.\n", @(infile))
end // end of [typecheck_file]

extern
fun ccomp_file_to_file_exec (i: int, s1: string, s2: string): void
  = "ccomp_file_to_file_exec"

implement ccomp_file_to_file_err (flag, infile, outfile) = let
  fn cmd ():<cloptr1> void = ccomp_file_to_file_exec (flag, infile, outfile)
in
  fork_and_exec_and_wait (cmd)
end // end of [ccomp_file_to_file_err]

implement ccomp_file_to_file (flag, infile, outfile) = let
  val status = ccomp_file_to_file_err (flag, infile, outfile)
in
  if (status <> 0) then exit_prerrf {void}
    (status, "Exit: [ccomp_file_to_file(%s, %s)] failed.\n", @(infile, outfile))
end // end of [ccomp_file_to_file]

implement ccomp_file (flag, infile): void = let
  val basename = basename_of_filename infile
  val outfile_c = basename + ".c"
in
  ccomp_file_to_file (flag, infile, outfile_c)
end // end of [ccomp_file]

(* ****** ****** *)

%{^

#include <errno.h>
#include <unistd.h>

//

extern ats_ptr_type atsopt_global ;

//

ats_void_type
typecheck_file_exec
  (ats_int_type flag, ats_ptr_type infile)
{
  int ret ;
  char *flag_str ;

  switch (flag) {
    case 0: flag_str = "--static" ; break ;
    case 1: flag_str = "--dynamic" ; break ;
    default:
      ats_exit_errmsg (
        1, "[ccomp_file_to_file_exec] failed: wrong flag.\n"
      ) ;
  }

  execl(
    (char *)atsopt_global,
    (char *)atsopt_global,
    "--typecheck", flag_str, infile,
    (char *)0
  ) ;
  if (!ret) perror ("execl failed: ") ;
  exit (errno) ;
}

//

ats_void_type
ccomp_file_to_file_exec
  (ats_int_type flag, ats_ptr_type infile, ats_ptr_type outfile)
{
  int ret ;
  char *flag_str ;

  switch (flag) {
    case 0: flag_str = "--static" ; break ;
    case 1: flag_str = "--dynamic" ; break ;
    default:
      ats_exit_errmsg (
        1, "[ccomp_file_to_file_exec] failed: wrong flag.\n"
      ) ;
  }

  execl(
    (char *)atsopt_global,
    (char *)atsopt_global,
    "--output", outfile, flag_str, infile,
    (char *)0
  ) ;
  if (!ret) perror ("execl failed: ") ;
  exit (errno) ;
}

%}

(* ****** ****** *)

(* end of [atscc.dats] *)
