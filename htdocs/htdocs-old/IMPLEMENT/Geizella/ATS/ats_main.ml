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

(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)

open Ats_misc

module Arg = Ats_arg
module Cnt = Ats_counter
module Err = Ats_error
module Fil = Ats_filename
module Par = Ats_parser
module StrPar = Ats_string_parser
module Env1 = Ats_env1
module Tr1 = Ats_trans1
module Env2 = Ats_stadynenv2
module Tr2 = Ats_trans2
module Env3 = Ats_staenv3
module Tr3 = Ats_trans3
module Tr4 = Ats_trans4

module CS = Ats_constraint

module Backend = Backend

(* ****** ****** *)

let geizella_dir: string =
  try Sys.getenv "GEIZELLA"
  with Not_found -> begin
    prerr_line "The environment variable <GEIZELLA> is undefined!" ;
    Err.abort ()
  end

(* ****** ****** *)

let initialize () = begin
  Cnt.initialize ();
  StrPar.initialize ();
  Tr1.initialize ();
  Tr2.initialize ();
end

(* ****** ****** *)

let load_fixity (): unit = (* load in built-in fixity declarations *)
  let is_done: bool ref = ref false in (* only done once *)
  let name = Filename.concat geizella_dir "prelude/fixity.ats" in
  let f = Fil.filename_make name in
  let prompt: out_channel -> unit =
    function out -> (fprint_string out name; fprint_string out ": ") in
    if not (!is_done) then
      let () = is_done := true in
      let ic = open_in name in
      let () = Fil.filename_push f in
      let ds = Par.parse_dec_from_channel true prompt ic in
      let () = Fil.filename_pop () in
      let ds1 = Tr1.dec_list_tr ds in
	Env1.env_make_top_pervasive ()
    else ()

let load_stafile (filename: string): unit =
  let is_done: bool ref = ref false in (* only done once *)
  let name = Filename.concat geizella_dir filename in
  let f = Fil.filename_make name in
  let prompt: out_channel -> unit =
    function out -> (fprint_string out name; fprint_string out ": ") in
    if not (!is_done) then
      let () = is_done := true in
      let ic = open_in name in
      let () = Fil.filename_push f in
      let ds = Par.parse_dec_from_channel true prompt ic in
      let () = Fil.filename_pop () in
      let () = close_in ic in
      let ds1 = Tr1.dec_list_tr ds in
      let ds2 = Tr2.dec1_list_tr ds1 in
      let () = Env2.stadynenv2_pervasive () in
	()
    else ()

let usage (cmd: string): unit = begin
  Printf.printf "usage: %s <command> ... <command>\n\n" cmd;
  print_string "where a <command> is of one of the following forms:\n\n";
  print_string "  -s filename (for statically loading <filename>)\n";
  print_string "  --static filename (for statically loading <filename>)\n";
  print_string "  -d filename (for dynamically loading <filename>)\n";
  print_string "  --dynamic filename (for dynamically loading <filename>)\n";
  print_string "  -o filename (output into <filename>)\n";
  print_string "  --output filename (output into <filename>)\n";
  print_string "  -h (for printing the usage)\n";
  print_string "  --help (for printing the usage)\n";
  print_newline ()
end

let prelude_stafiles: string list = [
  "prelude/param.ats";
  "prelude/stacst.ats";
  "prelude/sortdef.ats";
  "prelude/stadyncst.ats";

  "prelude/arith.sats";
  "prelude/vcontain.sats";

  "prelude/char.sats";
  "prelude/float.sats";
  "prelude/integer.sats";
  "prelude/pointer.sats";
  "prelude/printf.sats";
  "prelude/memory.sats";

  "prelude/array.sats";
  "prelude/list.sats";
  "prelude/option.sats";
  "prelude/reference.sats";
  "prelude/string.sats";
  "prelude/cstring.sats";

  "prelude/config/stdint.sats";

]

let load_prelude () = begin
  load_fixity ();
  List.iter load_stafile prelude_stafiles;
end

(* ****** ****** *)

let the_out_channel: (out_channel option) ref = ref None
let out_channel_get (): out_channel =
  match !the_out_channel with Some oc -> oc | None -> stdout
let out_channel_set (oc: out_channel) =
  let () = match !the_out_channel with
    | Some oc -> close_out oc | None -> () in
    the_out_channel := Some oc
let out_channel_reset () =
  let () = match !the_out_channel with
    | Some oc -> close_out oc | None -> () in
    the_out_channel := None

type command_kind =
  | CKnone
  | CKinput of bool (* is_static *)
  | CKoutput

(* ****** ****** *)

let main (argv: string array): unit =
  let is_prelude: bool ref = ref false in
  let the_command_kind: command_kind ref = ref CKnone in
  let is_wait: bool ref = ref true in
  let () = initialize () in
  let rec loop (args: Arg.arg_t list): unit = match args with
    | arg :: args -> begin match arg with
        | Arg.Key (0, name) -> begin match !the_command_kind with
	    | CKinput is_static ->
		let () = is_wait := false in
		let prompt out = (fprint_string out name; fprint_string out ": ") in
		let () =
		  if not (!is_prelude) then (is_prelude := true; load_prelude ()) in
		let () = Tr3.initialize () in
		let f = Fil.filename_make name in
		let in_channel = open_in name in
		let () = Fil.filename_push f in
		let ds =
		  Par.parse_dec_from_channel is_static prompt in_channel in
		let () = Fil.filename_pop () in
		let () = close_in in_channel in
		let ds1 = Tr1.dec_list_tr ds in
		let ds2 = Tr2.dec1_list_tr ds1 in
		let ds3 = Tr3.dec2_list_tr ds2 in
		let c3t = Tr3.finalize () in
(*
	        let () =
	          Printf.fprintf stdout "the constraint is:\n%a\n"
		    Ats_staenv3.fprint_cstr3 c3t in
*)
		let () = CS.cstr3_solve_init c3t in
		let () =
		  Printf.fprintf stdout
		    "\nThe phase of type inference is successfully completed!\n" in
		let () = Tr4.initialize () in
		let hids = Tr4.dec3_list_tr ds3 in
		let out_channel = out_channel_get () in
		let () =
		  let id = Fil.filename_get_fullname f in
		    Backend.do_backend hids out_channel is_static id in
		  loop args
	    | CKoutput ->
		let () = the_command_kind := CKnone in
		let oc = open_out name in (out_channel_set oc; loop args)
	    | CKnone -> loop args
	  end

        | Arg.Key (1, s) ->
	    let () = 
	      match s with
		| "s" -> (the_command_kind := CKinput true; is_wait := true)
		| "d" -> (the_command_kind := CKinput false; is_wait := true)
		| "o" -> the_command_kind := CKoutput
		| "h" -> (the_command_kind := CKnone; usage (argv.(0)))
		| _ -> () in
              loop args

        | Arg.Key (2, s) ->
	    let () = 
	      match s with
		| "static" -> (the_command_kind := CKinput true; is_wait := true)
		| "dynamic" -> (the_command_kind := CKinput false; is_wait := true)
		| "output" -> the_command_kind := CKoutput
		| "help" -> (the_command_kind := CKnone; usage (argv.(0)))
		| _ -> () in
              loop args

        | _ -> loop args
      end

    | [] when !is_wait -> begin match !the_command_kind with
	| CKinput is_static ->
	    let prompt out = fprint_string out "stdin: " in
	    let () =
	      if not (!is_prelude) then (is_prelude := true; load_prelude ()) in
	    let () = Tr3.initialize () in
	    let () = Fil.filename_push Fil.stdin in
	    let ds = Par.parse_dec_from_channel is_static prompt stdin in
	    let () = Fil.filename_pop () in
	    let ds1 = Tr1.dec_list_tr ds in
	    let ds2 = Tr2.dec1_list_tr ds1 in
	    let ds3 = Tr3.dec2_list_tr ds2 in
	    let c3t = Tr3.finalize () in
	    let () = CS.cstr3_solve_init c3t in
	    let () =
	      Printf.fprintf stdout
		"\nThe phase of type inference is successfully completed!\n" in
	    let () = Tr4.initialize () in
	    let hids = Tr4.dec3_list_tr ds3 in
	    let out_channel = out_channel_get () in
	    let () = Backend.do_backend hids out_channel is_static "stdin" in
	      ()
	| _ -> ()
      end

    | [] -> () in

    match Arg.args_parse argv with
      | [] -> error_of_deadcode "ats_main.ml: argv is empty!"
      | _ :: args -> loop args

let () =
  try (main Sys.argv; out_channel_reset ())
  with exn -> (out_channel_reset (); raise exn)
