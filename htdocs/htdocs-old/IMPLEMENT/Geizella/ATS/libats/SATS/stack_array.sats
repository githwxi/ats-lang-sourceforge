(*******************************************************************)
(*                                                                 *)
(*                        Applied Type System                      *)
(*                                                                 *)
(*                          (c) Hongwei Xi                         *)
(*                                                                 *)
(*                            2002 - 2007                          *)
(*                                                                 *)
(*                         Boston University                       *)
(*                                                                 *)
(*                   Distributed by permission only.               *)
(*                                                                 *)
(*******************************************************************)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

absviewtype stack_array (elt:viewtype, sz:int, sz_max:int)

fun{a:viewtype} stack_array_make {sz_max:nat}
  (max: int sz_max):<> [l:addr] (stack_array (a, 0, sz_max) @ l | ptr l)

fun{a:viewtype} stack_array_free {sz_max:nat} {l:addr}
  (pf: stack_array (a, 0, sz_max) @ l | p: ptr l):<> void

(* ****** ****** *)

fun{a:viewtype} stack_array_size
  {sz,sz_max:int | 0 <= sz; sz <= sz_max} {l:addr}
  (pf: !stack_array (a, sz, sz_max) @ l | p: ptr l):<> int sz

(* ****** ****** *)

fun{a:viewtype} stack_array_is_empty :
  {sz,sz_max:int | 0 <= sz; sz <= sz_max} {l:addr}
  (pf: !stack_array (a, sz, sz_max) @ l | p: ptr l):<> bool (sz == 0)

fun{a:viewtype} stack_array_is_full
  {sz,sz_max:int | 0 <= sz; sz <= sz_max} {l:addr}
  (pf: !stack_array (a, sz, sz_max) @ l | p: ptr l):<> bool (sz == sz_max)

(* ****** ****** *)

fun{a:viewtype} stack_array_pop :
  {sz,sz_max:int | 0 < sz; sz <= sz_max} {l:addr}
  (pf: stack_array (a, sz, sz_max) @ l >>
       stack_array (a, sz-1, sz_max) @ l | p: ptr l):<> a

fun{a:viewtype} stack_array_push :
  {sz,sz_max:int | 0 <= sz; sz < sz_max} {l:addr}
  (pf: stack_array (a, sz, sz_max) @ l >>
       stack_array (a, sz+1, sz_max) @ l | p: ptr l, x: a):<> void

(* ****** ****** *)

// end of stack_array.sats
