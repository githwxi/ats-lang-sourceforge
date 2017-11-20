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

// defined in dirent.cats
abst@ype DIR = $extype "ats_DIR_type"
abst@ype dirent = $extype "ats_dirent_type"
abst@ype off_t = $extype "ats_off_t_type"

fun closedir_err {l_dir:addr} (pf: DIR @ l_dir | p: ptr l_dir): int
  = "atslib_closedir_err"

fun closedir {l_dir:addr} (pf: DIR @ l_dir | p: ptr l_dir): void
  = "atslib_closedir"  

fun opendir_err (s: string)
  : [l_dir:addr] (option_v (DIR @ l_dir, l_dir <> null) | ptr l_dir)
  = "atslib_opendir_err"

fun opendir (s: string) : [l_dir:addr] (DIR @ l_dir | ptr l_dir)
  = "atslib_opendir"

fun readdir_err (dir: &DIR)
  : [l_ent:addr] (option_v (vbox (dirent @ l_ent), l_ent <> null) | ptr l_ent)
  = "atslib_readdir_err"

fun rewinddir (dir: &DIR): void = "atslib_rewinddir"

fun telldir (dir: &DIR): off_t

fun seekdir (dir: &DIR, off: off_t): void

(* ****** ****** *)

(* end of [dirent.sats] *)
