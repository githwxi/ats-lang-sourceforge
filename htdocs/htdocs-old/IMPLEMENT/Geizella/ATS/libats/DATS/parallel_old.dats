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
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

// Time: March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

// Some functions for supporting multicore programming

//
// This is the *first* concrete example I did in which
// a (simple) locking order is statically enforced to
// prevent potential deadlocks. Though the underlying
// strategy is quite involved and certainly needs some
// improvement, the result it ensures is gratifying!
//

(* ****** ****** *)

%{^

#ifndef ATS_MULTITHREAD
#define ATS_MULTITHREAD
#endif

#include "libats/CATS/thunk.cats"

#include "libc/CATS/pthread.cats"
#include "libc/CATS/pthread_locks.cats"

%}

staload "libats/SATS/thunk.sats"

staload "libc/SATS/pthread.sats"
staload "libc/SATS/pthread_locks.sats"

(* ****** ****** *)

staload "libats/SATS/parallel.sats"

(* ****** ****** *)

abstype lock1_t // = mutexref_t (Thunkopt)
absview lock1_unlock_ticket (addr)
absview lockord1


abstype lock2_t // = mutexref_t (MClst)
absview lock2_unlock_ticket (addr)
absview lockord2

viewdef lockord12 = @(lockord1, lockord2)
extern prval parallel_spawn_lockordbox: vbox lockord12

(* ****** ****** *)

typedef C = ref (cond_vt)
typedef M = lock1_t
typedef MC = '{ m=M, c=C, id= int }
viewtypedef MClst = List_vt MC

typedef NTHREAD = lock2_t

(* ****** ****** *)

(*

//
// Here is the locking order:
//
// If [lock2] is locked, then [lock1] can no longer be locked
// until [lock2] is unlocked
//

*)

extern fun pthread_create_detach_lockord12
  (thunk: (!lockord12 | (*none*)) -<lin,cloptr1> void): void
  = "ats_pthread_create_detach"

extern fun lock1_create_tsz {l:addr} (
    pf: !Thunkopt @ l >> Thunkopt? @ l
  | p: ptr l
  , tsz: sizeof_t (Thunkopt)
  ) : lock1_t
  = "atslib_pthread_mutexref_create_tsz"

extern fun lock1_lock
  (_ord1: lockord1, _ord2: !lockord2 | m: lock1_t)
  :<> [l:addr] (lock1_unlock_ticket l, Thunkopt @ l | ptr l)
  = "atslib_pthread_mutexref_lock"

extern fun lock1_unlock {l:addr}
  (_ticket: lock1_unlock_ticket l, _at: Thunkopt @ l | p: ptr l)
  :<> (lockord1 | void)
  = "atslib_pthread_mutexref_unlock"

extern fun cond_wait_lock1 {l:addr} (
    _ord2: !lockord2
  , _ticket: !lock1_unlock_ticket l
  , _at: !Thunkopt @ l
  | cond: &cond_vt
  , p: ptr l) :<> void
  = "atslib_pthread_cond_wait_mutexref"

//

extern fun lock2_create_tsz {l:addr} (
    pf: !MClst @ l >> MClst? @ l
  | p: ptr l
  , tsz: sizeof_t (MClst)
  ):<> lock2_t
  = "atslib_pthread_mutexref_create_tsz"

extern fun lock2_lock
  (_ord2: lockord2 | m: lock2_t)
  :<> [l:addr] (lock2_unlock_ticket l, MClst @ l | ptr l)
  = "atslib_pthread_mutexref_lock"

extern fun lock2_unlock {l:addr}
  (_ticket: lock2_unlock_ticket l, _at: MClst @ l | p: ptr l)
  :<> (lockord2 | void)
  = "atslib_pthread_mutexref_unlock"

(* ****** ****** *)

extern val parallel_nthread: NTHREAD

implement parallel_nthread = let
  var mcs: MClst = list_vt_nil ()
in
  lock2_create_tsz (view@ mcs | &mcs, sizeof<MClst>)
end

(* ****** ****** *)

fun worker_fun
  (pford12: !(lockord1, lockord2) | mc: MC): void = let
  prval @(pford1, pford2) = pford12
  val (pf1_ticket, pf1_at | ptr1) = lock1_lock (pford1, pford2 | mc.m)
  val (pford1 | ()) = worker_fun_cont (pford2, pf1_ticket, pf1_at | ptr1, mc)
in
  pford12 := @(pford1, pford2)
end

and worker_fun_cont {l:addr} (
    pford2: !lockord2
  , pf1_ticket: lock1_unlock_ticket l
  , pf1_at: Thunkopt @ l
  | ptr1: ptr l
  , mc: MC
  ) : @(lockord1 | void) = let
  val x = !ptr1; val () = !ptr1 := thunkopt_none
in
  if thunkopt_is_some (x) then let
    val x = thunkopt_unsome x; val () = thunk_exec (x)
    // make itself available
    val (pf2_ticket, pf2_at  | ptr2) = lock2_lock (pford2 | parallel_nthread)
    val () = (!ptr2 := list_vt_cons (mc, !ptr2))
    val (pford2_new | ()) = lock2_unlock (pf2_ticket, pf2_at | ptr2)
    prval () = (pford2 := pford2_new)
    val () = let
      val (vbox pf_cond | p_cond) = ref_get_view_ptr (mc.c)
    in
      cond_wait_lock1 (pford2, pf1_ticket, pf1_at | !p_cond, ptr1)
    end
  in
    worker_fun_cont (pford2, pf1_ticket, pf1_at | ptr1, mc)
  end else let
    val () = thunkopt_unnone (x)
    val () = let
      val (vbox pf_cond | p_cond) = ref_get_view_ptr (mc.c)
    in
      cond_wait_lock1 (pford2, pf1_ticket, pf1_at | !p_cond, ptr1)
    end
  in
    worker_fun_cont (pford2, pf1_ticket, pf1_at | ptr1, mc)
  end
end // end of [worker_fun_cont]

(* ****** ****** *)

local
  var ini: int = 0
  val nworker_ref: ref int = ref_make_elt_tsz (ini, sizeof<int>)
  var ini: int = 0
  val workerid_ref: ref int = ref_make_elt_tsz (ini, sizeof<int>)
in
  fn nworker_get (): int = !nworker_ref

  fn nworker_inc (): void = begin
    let val nworker = !nworker_ref in !nworker_ref := nworker + 1 end
  end

  fn nworker_dec (): void = begin
    let val nworker = !nworker_ref in !nworker_ref := nworker - 1 end
  end

  fn workerid_gen () = let
    val id = !workerid_ref; val () = !workerid_ref := id + 1
  in
    id
  end // end of [workerid_gen]
end // end of [local]

(* ****** ****** *)

implement parallel_nworker_get () = nworker_get ()

implement parallel_worker_add_one () = let
  var x: Thunkopt = thunkopt_none
  val m = lock1_create_tsz (view@ x | &x, sizeof<Thunkopt>)
  val (pf_gc, pf_at | ptr) = pthread_cond_create ()
  val (pfbox | ()) = vbox_make_view_ptr_gc (pf_gc, pf_at | ptr)
  val c = ref_make_view_ptr (pfbox | ptr)
  val mc: MC = '{ m=m, c=c, id= workerid_gen () }
  val () = let
    prval vbox pford12 = parallel_spawn_lockordbox
    prval @(pford1, pford2) = pford12
    val (pf2_ticket, pf2_at  | ptr2) = lock2_lock (pford2 | parallel_nthread)
    val () = (!ptr2 := list_vt_cons (mc, !ptr2))
    val (pford2 | ()) = lock2_unlock (pf2_ticket, pf2_at | ptr2)
  in
    pford12 := @(pford1, pford2)
  end
  val () = pthread_create_detach_lockord12
    (llam (pf | (*none*)) => worker_fun (pf | mc))
  val () = nworker_inc ()
in
  // empty
end

implement parallel_worker_add_many (n) = begin
  if n > 0 then begin
    parallel_worker_add_one (); parallel_worker_add_many (n-1)
  end
end // end of [worker_thread_add_many]

(* ****** ****** *)

fun parallel_spawn_lockord12 {v:view}
  (pford12: !lockord12 | linclo: () -<lin,cloptr1> (v | void))
  : lockview (v) = let
  prval @(pford1, pford2) = pford12
  val (pf2_ticket, pf2_at | ptr2) = lock2_lock (pford2 | parallel_nthread)
in
  case+ !ptr2 of
  | ~list_vt_cons (mc, mcs) => let
      val () = (!ptr2 := mcs)
      val (pford2 | ()) = lock2_unlock (pf2_ticket, pf2_at | ptr2)
      val lock = pthread_uplock_create {v} ()
      val ticket = pthread_upticket_create (lock)
      val thunk = thunk_make (
        llam () => let
          val (pf | ()) = linclo (); val () = cloptr_free (linclo)
        in
          pthread_upticket_load_and_destroy (pf | ticket)
        end
      ) // end of [thunk_make_linclo]
      val (pf1_ticket, pf1_at | ptr1) = lock1_lock (pford1, pford2 | mc.m)
      val x = !ptr1; val () = (!ptr1 := thunkopt_some (thunk))
      val () = let
        val (vbox pf_cond | p_cond) = ref_get_view_ptr (mc.c)
      in
        $effmask_all (pthread_cond_signal (!p_cond))
      end
      val (pford1 | ()) = lock1_unlock (pf1_ticket, pf1_at | ptr1)
      prval () = (pford12 := @(pford1, pford2))
      val () = assert_errmsg (
        thunkopt_is_none x, "libats: parallel.dats: parallel_spawn_lockord12"
      )
      val () = thunkopt_unnone (x)
    in
      LOCKVIEWlock lock
    end
  | list_vt_nil () => let
      val () = fold@ (!ptr2)
      val (pford2 | ()) = lock2_unlock (pf2_ticket, pf2_at | ptr2)
      prval () = (pford12 := @(pford1, pford2))
      val (pf | ()) = linclo (); val () = cloptr_free (linclo)
    in
      LOCKVIEWview (pf | (*none*))
    end
end // end of [parallel_spawn_lock12]

implement parallel_spawn (linclo) = let
  prval vbox pford12 = parallel_spawn_lockordbox
in
  $effmask_all (parallel_spawn_lockord12 (pford12 | linclo))
end

implement parallel_sync (ret) = begin case+ ret of
  | ~LOCKVIEWlock lock => pthread_uplock_destroy (lock)
  | ~LOCKVIEWview (pf | (*none*)) => (pf | ())
end // end of [parallel_sync]

(* ****** ****** *)

(* end of [parallel.dats] *)
