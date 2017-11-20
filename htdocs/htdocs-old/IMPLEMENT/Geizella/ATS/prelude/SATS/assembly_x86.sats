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

// for x86 assembly programming

#if VERBOSE #then

#warning "Loading assembly_x86.ats starts!\n"

#endif

(* ****** ****** *)

sta eax : reg // accumulator for operands and results data
and ebx : reg // pointer to data in the DS segment
and ecx : reg // counter for string and loop operations
and edx : reg // I/O pointer

sta esi : reg // source pointer for string operations
and edi : reg // destination pointer for string operations

sta esp : reg // stack pointer (in the SS segment)
and ebp : reg // pointer to data on the stack (in the SS segment)

val add_reg_imm :
  {r:reg} {i,j:int} (int i @ r, int j) -<> int (i+j) @ r

val sub_reg_imm :
  {r:reg} {i,j:int} (int i @ r, int j) -<> int (i-j) @ r

(* ****** ****** *)

#if VERBOSE #then

#warning "Loading assembly_x86.ats finishes!\n"

#endif

(* end of [assembly_x86] *)
