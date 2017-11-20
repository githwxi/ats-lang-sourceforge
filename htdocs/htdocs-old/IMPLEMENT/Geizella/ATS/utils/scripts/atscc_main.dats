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

%{^

#include "libc/CATS/stdio.cats"
#include "libc/CATS/stdlib.cats"
#include "libc/CATS/unistd.cats"

typedef ats_ptr_type ats_intref_type ;

%}

staload "basics.sats"
staload "atscc.sats"

(* ****** ****** *)

fn do_usage (cmd: string): void = begin
  printf ("The usage of %s is:\n", @(cmd));
  printf ("  %s [flag-or-file]*\n", @(cmd));
end


#define nil strlst_nil
#define :: strlst_cons

fn string_is_flag (s: string):<fun0> bool =
  let
     val s = string1_of_string0 s
  in
     if string1_is_empty s then false else
       (string_get_char_at (s, 0) = '-')
  end

(* ****** ****** *)

fn flag_is_compile_only (flag: string):<fun0> Bool =
  case+ flag of
    | "-cc" => true
    | "--atscc" => true
    | _ => false

val is_compile_only: intref = intref_make 0
extern val "is_compile_only" = is_compile_only

fn flag_is_typecheck_only (flag: string):<fun0> Bool =
  case+ flag of
    | "-tc" => true
    | "--atstc" => true
    | _ => false

val is_typecheck_only: intref = intref_make 0
extern val "is_typecheck_only" = is_typecheck_only

fn flag_is_objcode_only (flag: string):<fun0> Bool =
  case+ flag of "-c" => true | _ => false

val is_objcode_only: intref = intref_make 0
extern val "is_objcode_only" = is_objcode_only

(* ****** ****** *)

fn flag_is_ATS_GC (flag: string): Bool =
  case+ flag of "-D__ATS_GC" => true | _ => false

val is_ATS_GC: intref = intref_make 0
extern val "is_ATS_GC" = is_ATS_GC

fn flag_is_ATS_gcats (flag: string): Bool =
  case+ flag of "-D__ATS_gcats" => true | _ => false

val is_ATS_gcats: intref = intref_make 0
extern val "is_ATS_gcats" = is_ATS_gcats

fn flag_is_ATS_gc (flag: string): Bool =
  case+ flag of "-D__ATS_gc" => true | _ => false

val is_ATS_gc: intref = intref_make 0
extern val "is_ATS_gc" = is_ATS_gc

(* ****** ****** *)

fn flag_is_ATS_MULTITHREAD (flag: string): Bool =
  case+ flag of "-DATS_MULTITHREAD" => true | _ => false

val is_ATS_MULTITHREAD = intref_make 0
extern val "is_ATS_MULTITHREAD" = is_ATS_MULTITHREAD

(* ****** ****** *)

extern
fun atscc_outfile_name_make (basename: string): String
  = "atscc_outfile_name_make"

(* ****** ****** *)
  
fun atscc_argv_process {n:pos} {l:addr}
  (pf: !array_v (String, n, l) | n: int n, p: ptr l):<fun1> Strlst = let
  fn* aux {i:nat | i <= n} // .<n-i,0>.
    (pf: !array_v (String, n, l) | res: Strlst, i: int i):<cloptr1> Strlst =
    if i < n then
      let
         val s = p[i]
      in
         if string_is_flag s then aux_flag (pf | res, i, s)
         else aux_file (pf | res, i, s)
      end           
    else if intref_get is_objcode_only > 0 then
      let
        val res = strlst_reverse res
        val _IATSHOME = "-I" + ATSHOME
        val _Iruntime_global = "-I" + runtime_global
      in
        _IATSHOME :: _Iruntime_global :: res
      end
    else begin
      let
        val ats_prelude_c = runtime_global + "ats_prelude.c"
        val res = ats_prelude_c :: res
        val res: Strlst =
          if intref_get is_ATS_GC > 0 then "-lgc" :: res
          else if intref_get is_ATS_gcats > 0 then
            let val gc_o = runtime_global + "gcats/gc.o" in gc_o :: res end
          else if intref_get is_ATS_gc > 0 then let
            val gcobj_local: string = begin
              if intref_get is_ATS_MULTITHREAD > 0 then "gc/gc_mt.o"
              else "gc/gc.o"
            end
            val gcobj_global: string = runtime_global + gcobj_local
          in
            gcobj_global :: res end
          else res
        val res = "-lats" :: res
        val res = strlst_reverse res
        val _Latslib_global = "-L" + atslib_global
        val _IATSHOME = "-I" + ATSHOME
        val _Iruntime_global = "-I" + runtime_global
      in
        _IATSHOME :: _Iruntime_global :: _Latslib_global :: res
      end
    end

  and aux_flag {i:nat | i < n} // .<n-i-1,1>.
    (pf: !array_v (String, n, l) |
     res: Strlst, i: int i, flag: String):<cloptr1> Strlst = begin
    case+ flag of
    | _ when flag_is_compile_only flag => begin
        intref_set (is_compile_only, 1); aux (pf | res, i+1)
      end
    | _ when flag_is_typecheck_only flag => begin
        intref_set (is_typecheck_only, 1); aux (pf | res, i+1)
      end
    | _ when flag_is_objcode_only flag => begin
        intref_set (is_objcode_only, 1); aux (pf | flag :: res, i+1)
      end
    | _ when flag_is_ATS_GC flag => begin
        intref_set (is_ATS_GC, 1); aux (pf | flag :: res, i+1)
      end
    | _ when flag_is_ATS_gcats flag => begin
        intref_set (is_ATS_gcats, 1); aux (pf | flag :: res, i+1)
      end
    | _ when flag_is_ATS_gc flag => begin
        intref_set (is_ATS_gc, 1); aux (pf | flag :: res, i+1)
      end
    | _ when flag_is_ATS_MULTITHREAD flag => begin
        intref_set (is_ATS_MULTITHREAD, 1); aux (pf | flag :: res, i+1)
      end
    | _ => aux (pf | flag :: res, i+1)
  end // end of [aux_flag]

  and aux_file {i:nat | i < n} // .<n-i-1,1>.
    (pf: !array_v (String, n, l) |
     res: Strlst, i: int i, file: String):<cloptr1> Strlst = let
    val sfx = suffix_of_filename file
    val flag: int =
      if stropt_is_none sfx then ~1 else begin
        case stropt_unsome sfx of
        | "sats" => 0 | "dats" => 1 | _ => ~1
      end
  in
    if flag >= 0 then
      if intref_get (is_typecheck_only) > 0 then let
        val () = typecheck_file (flag, file)
      in
        aux (pf | res, i+1)
      end else let 
        val basename = basename_of_filename file
        val outfile_c = atscc_outfile_name_make basename
        val () = ccomp_file_to_file (flag, file, outfile_c)
      in
        aux (pf | outfile_c :: res, i+1)
      end
    else begin
      aux (pf | file :: res, i+1)
    end
  end // end of [aux_file]
in
  aux (pf | nil (), 1)
end

extern val "atscc_argv_process" = atscc_argv_process

//

dynload "basics.dats"
dynload "atscc.dats"

//

implement main_prelude () = ()

//

extern
fun __ats_main {n:pos} (argc: int n, argv: &(@[String][n])): void
  = "__ats_main"

implement main (argc, argv) = case+ argc of
  | 1 => let val cmd = argv.[0] in do_usage (basename_of_filename cmd) end
  | _ => __ats_main (argc, argv)

%{

//

typedef ats_ptr_type ats_stropt_type ;
typedef ats_ptr_type ats_string_type ;

extern ats_string_type strlst_head(ats_ptr_type) ;

extern ats_ptr_type strlst_tail(ats_ptr_type) ;

extern ats_int_type strlst_length(ats_ptr_type) ;

extern ats_ptr_type strlst_reverse(ats_ptr_type) ;

//

extern ats_intref_type is_compile_only ;
extern ats_intref_type is_typecheck_only ;
extern ats_int_type inref_get(ats_intref_type) ;

ats_string_type
atscc_outfile_name_make (ats_string_type basename) {
  int n ; char c, *s ;
  n = strlen((char *)basename) ;
  s = (char *)ats_malloc_gc(n+3) ;
  s[n+2] = '\000' ; s[n+1] = 'c' ; s[n] = '.' ; --n ;
  while (n >= 0) {
    c = ((char *)basename)[n] ;
    if (c == '.') { s[n] = '_' ; --n ; break ; }
    s[n] = c ; --n ;
  }
  while (n >= 0) { s[n] = ((char *)basename)[n] ; --n ; }
  return s ;
}

ats_void_type
__ats_main (ats_int_type argc, ats_ptr_type argv) {
  int i, n ;
  ats_sum_ptr_type ss;
  ats_ptr_type argv_new, p;
  pid_t pid;
  int status;

  ss = ((ats_sum_ptr_type (*)(ats_int_type, ats_ptr_type))atscc_argv_process)(argc, argv) ;

  if (intref_get(is_typecheck_only) > 0) return ;
  if (intref_get(is_compile_only) > 0) return ;

  n = strlst_length(ss) ;
  argv_new = ats_malloc_ngc ((n+1)*sizeof(ats_string_type)+sizeof(ats_stropt_type)) ;
  p = argv_new;

  *((ats_string_type *)p) = "gcc";
  p = ((ats_string_type *)p) + 1;
  for (i = 0; i < n; ++i) {
    *((ats_string_type *)p) = strlst_head(ss);
    p = ((ats_string_type *)p) + 1;
    ss = strlst_tail(ss);
  }
  *((ats_stropt_type *)p) = (ats_stropt_type)0;

  // printf ("argv_new = ") ;
  for (i = 0; i <= n; ++i)
    printf ("%s ", ((ats_string_type *)argv_new)[i]) ;
  printf ("\n") ;

  pid = fork () ;
  if (pid < 0) {
    ats_exit_errmsg (errno, "Exit: [fork] failed.\n") ;
  }
  if (pid == 0) execvp ("gcc", argv_new) ; // this is the child
  wait (&status) ; // this parent
  if (status)
    atspre_exit_prerrf (status, "Exit: [gcc] failed.\n");
  return ;
}

%}

(* ****** ****** *)

(* end of [atscc_main.dats] *)
