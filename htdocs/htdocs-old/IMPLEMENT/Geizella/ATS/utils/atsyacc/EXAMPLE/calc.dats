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
 * ATS is  free software;  you can redistribute it and/or modify it under
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
 * along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
 * Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

%{^

#include "libc/CATS/stdio.cats"

%}

staload "libc/SATS/stdio.sats"
staload "utils/atslex/lexing.sats"

dataviewtype exp =
  | EXPide of string
  | EXPint of int
  | EXPadd of (exp, exp)
  | EXPsub of (exp, exp)
  | EXPmul of (exp, exp)
  | EXPdiv of (exp, exp)

extern fun exp_ide (s: string): exp = "exp_ide"
extern fun exp_int (i: int): exp = "exp_int"
extern fun exp_add (e1: exp, e2: exp): exp = "exp_add"
extern fun exp_sub (e1: exp, e2: exp): exp = "exp_sub"
extern fun exp_mul (e1: exp, e2: exp): exp = "exp_mul"
extern fun exp_div (e1: exp, e2: exp): exp = "exp_div"

implement exp_ide (id) = EXPide (id)
implement exp_int (i) = EXPint (i)
implement exp_add (e1, e2) = EXPadd (e1, e2)
implement exp_sub (e1, e2) = EXPsub (e1, e2)
implement exp_mul (e1, e2) = EXPmul (e1, e2)
implement exp_div (e1, e2) = EXPdiv (e1, e2)

dataviewtype cmd =
  | CMDassgn of (string, exp)
  | CMDerror
  | CMDprint of exp
  | CMDquit

extern fun cmd_assgn (s: string, e: exp): cmd = "cmd_assgn"
extern fun cmd_error (): cmd = "cmd_error"
extern fun cmd_print (e: exp): cmd = "cmd_print"
extern fun cmd_quit (): cmd = "cmd_quit"

implement cmd_assgn (id, e) = CMDassgn (id, e)
implement cmd_error () = CMDerror ()
implement cmd_print (e) = CMDprint (e)
implement cmd_quit () = CMDquit ()

(* ****** ****** *)

fun free_exp (e0: exp): void =
  case+ e0 of
    | ~EXPide id => ()
    | ~EXPint i => ()
    | ~EXPadd (e1, e2) => (free_exp e1; free_exp e2)
    | ~EXPsub (e1, e2) => (free_exp e1; free_exp e2)
    | ~EXPmul (e1, e2) => (free_exp e1; free_exp e2)
    | ~EXPdiv (e1, e2) => (free_exp e1; free_exp e2)

fun free_cmd (cmd: cmd): void =
  case+ cmd of
    | ~CMDassgn (id, e) => free_exp e
    | ~CMDerror () => ()
    | ~CMDprint e => free_exp e
    | ~CMDquit () => ()

//

exception EvalErrorException

(*

[var] := [identifier]
[exp0] :=  [var] | [integer] | ( [exp2] )
[exp0_r] := * [exp0] | / [exp0] | (* empty *)
[exp1] := [exp0] [exp1_r]
[exp1_r] := + [exp1] | - [exp1] | (* empty *)
[exp2] := [exp1] [exp1_r]

*)

//

datatype env = ENVnil | ENVcons of (string, int, env)

fun print_env (env: env): void = case+ env of
  | ENVcons (id, i, env) =>
    (print id; print " = "; print i; print_newline (); print_env env)
  | ENVnil () => ()

fun env_find (env: env, id0: string): int =
  case+ env of
    | ENVcons (id, i, env) =>
      if id0 = id then i else env_find (env, id0)
    | ENVnil () => 0

fun eval_exp (env: &env, e0: exp): int = begin
  case+ e0 of
  | ~EXPint i => i
  | ~EXPadd (e1, e2) => eval_exp (env, e1) + eval_exp (env, e2)
  | ~EXPsub (e1, e2) => eval_exp (env, e1) - eval_exp (env, e2)
  | ~EXPmul (e1, e2) => eval_exp (env, e1) * eval_exp (env, e2)
  | ~EXPdiv (e1, e2) => eval_exp (env, e1) / eval_exp (env, e2)
  | ~EXPide (id) => env_find (env, id)
end // end of [eval_exp]

fun eval_cmd (env: &env, cmd: cmd): int =
  case+ cmd of
    | ~CMDassgn (id, e) =>
      let val i = eval_exp (env, e) in
(*
        print "eval_cmd: before:\n"; print_env env;
*)
        env := ENVcons (id, i, env);
(*
        print "eval_cmd: after:\n"; print_env env;
*)
        0
      end
    | ~CMDprint e => 
      let val i = eval_exp (env, e) in
        print ">> "; print i; print_newline (); 0
      end
    | ~CMDquit () => 1
    | ~CMDerror () => begin
        print "The command is illegal; please try again:\n"; 0
      end
//

extern fun parse_cmd (): cmd = "parse_cmd"
extern fun getline (): string

fun eval_string (env: &env, input: string): int =
  let
    val (pf_infil | infil) = infile_make_string input
    val (pf_lexbuf | lexbuf) = lexbuf_make_infile (pf_infil | infil)
    val () = lexing_lexbuf_set (pf_lexbuf | lexbuf)
    val cmd = parse_cmd ()
  in
    eval_cmd (env, cmd)
  end

(* ****** ****** *)

dynload "utils/atslex/lexing.dats"
dynload "calc_lats.dats"

implement main (argc, argv) = let

var env0: env = ENVnil ()

fun read_eval_print (env: &env): void =
  let
    val () = print "<< "
    val () = fflush_stdout ()
    val input = getline ()
(*
    val () = prerr ("read_eval_print: getline()\n")
*)
    val i = eval_string (env, input)
    val () = lexing_lexbuf_free ()
  in    
    if i = 0 then read_eval_print (env) else ()
  end

in

read_eval_print (env0)

end

(* ****** ****** *)

dataviewtype charlst (int) =
  | charlst_nil (0)
  | {n:nat} charlst_cons (n+1) of (char, charlst n)

#define nil charlst_nil
#define :: charlst_cons
#define cons charlst_cons

extern fun charlst_is_nil {n:nat} (cs: !charlst n): bool (n == 0) =
  "charlst_is_nil"

implement charlst_is_nil (cs) = case+ cs of
  | nil _ => (fold@ cs; true) | cons _ => (fold@ cs; false)

extern fun
charlst_uncons {n:pos} (cs: &charlst n >> charlst (n-1)): char =
  "charlst_uncons"

implement charlst_uncons (cs) =
  let val ~(c :: cs_r) = cs in cs := cs_r; c end

extern fun
string_make_charlst_int {n:nat} (cs: charlst n, n: int n): string n =
  "string_make_charlst_int"

%{

ats_ptr_type
string_make_charlst_int (ats_ptr_type cs, const ats_int_type n) {
  char *s0, *s;

  s0 = ats_malloc_gc(n+1) ;
  s = s0 + n ;
  *s = '\0' ; --s ;

  while (!charlst_is_nil(cs)) { *s = charlst_uncons(&cs) ; --s ; }

  return s0 ;
}

%}

implement getline () = let
  fun loop {n:nat} (cs: charlst n, n: int n): string =
    let val c = getchar () in
      if c >= 0 then begin
        case+ char_of_int c of
          | '\n' => string_make_charlst_int (cs, n)
          | c => loop (charlst_cons (c, cs), n+1)
      end else begin
        string_make_charlst_int (cs, n)
      end
    end
in
  loop (charlst_nil (), 0)
end
