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

abstype deque (elt:type+, size:int) 

exception DequeSubscriptException

(* ****** ****** *)

val deque_nil : {a:type} deque (a, 0)
fun deque_is_empty {a:type} {n:nat} (q: deque (a, n)):<> bool (n==0)

(* ****** ****** *)

fun deque_cons {a:type} {n:nat} (x: a, q: deque (a, n)):<> deque (a, n+1)

fun deque_head
  {a:type} {n:pos} (q: deque (a, n)) -<> a

and deque_head_exn
  {a:type} {n:nat} (q: deque (a, n)):<!exn> [n>0] a

fun deque_tail
  {a:type} {n:pos} (q: deque (a, n)):<> deque (a, n-1)

and deque_tail_exn
  {a:type} {n:pos} (q: deque (a, n)):<!exn> [n>0] deque (a, n-1)

(* ****** ****** *)

fun deque_snoc {a:type} {n:nat} (x: a, q: deque (a, n)):<> deque (a, n+1)

fun deque_last
  {a:type} {n:pos} (q: deque (a, n)):<> a

and deque_last_exn
  {a:type} {n:nat} (q: deque (a, n)):<!exn> [n>0] a

fun deque_init
  {a:type} {n:pos} (q: deque (a, n)):<> deque (a, n-1)

and deque_init_exn
  {a:type} {n:pos} (q: deque (a, n)):<!exn> [n>0] deque (a, n-1)

(* ****** ****** *)

// end of deque_fun.sats
