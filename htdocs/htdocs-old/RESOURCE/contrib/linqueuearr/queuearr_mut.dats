(*
**
** An implementation of multithread queues based on arrays
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

staload "libc/SATS/pthread.sats"

(* ****** ****** *)

staload LQA = "linqueuearr.dats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

abstype queuearr_mut_t (a:viewt@ype)

(* ****** ****** *)

absview ISEMP (int, addr); absview ISFUL (int, int, addr)

absview queuearr_lock_v (a:viewt@ype, l:addr)

viewtypedef queuearr_mut_struct
  (a:viewt@ype, m:int, n:int, l:addr) = @{
  queue= $LQA.linqueuearr_vt (a, m, n)
, queue_mutex= mutex_vt (queuearr_lock_v (a, l))
, isemp_view= ISEMP (n, l)
, isemp_cond= cond_vt // signaling the transition: n = 0 -> n > 0 
, isful_view= ISFUL (m, n, l)
, isful_cond= cond_vt // signaling the transition: m = n -> m > n
} // end of [queuearr_mut_vt]

extern typedef "queuearr_mut_struct" = queuearr_mut_struct (void, 0, 0, null)

(* ****** ****** *)

extern prfun queuearr_lock_v_fold
  {a:viewt@ype} {m,n:nat | n <= m} {l:addr}
    (pf: queuearr_mut_struct (a, m, n, l) @ l):<prf> queuearr_lock_v (a, l)

extern prfun queuearr_lock_v_unfold
  {a:viewt@ype} {l:addr} (pf: queuearr_lock_v (a, l))
    :<prf> [m,n:nat | n <= m] queuearr_mut_struct (a, m, n, l) @ l

(* ****** ****** *)

extern prfun isemp_dec_prfun
  {n:pos} {l:addr} (pf: !ISEMP (n, l) >> ISEMP (n-1, l)):<prf> void

extern prfun isful_inc_prfun
  {m,n:nat | n < m} {l:addr} (pf: !ISFUL (m,n,l) >> ISFUL (m,n+1,l)):<prf> void

(* ****** ****** *)

extern fun{} isemp_inc_fun {n:nat} {l:addr}
  (pf: !ISEMP (n, l) >> ISEMP (n+1, l) | n: int n, p: ptr l):<1,~ref> void

implement{} isemp_inc_fun {n} {l} (pf | n, p) = let
  prval pfstruct = queuearr_mut_struct_make () where {
    extern prfun queuearr_mut_struct_make
      ():<prf> queuearr_mut_struct (void, 0, 0, l) @ l
  } // end of [prval]
  // [pthread_cond_broadcast]: wake up all the waiting threads
  val () = if n = 0 then pthread_cond_broadcast (p->isemp_cond)
  prval () = queuearr_mut_struct_free (pfstruct) where {
    extern prfun queuearr_mut_struct_free
      (_: queuearr_mut_struct (void, 0, 0, l) @ l):<prf> void
  } // end of [prval]
  prval () = isemp_inc_prfun (pf) where {
    extern prfun isemp_inc_prfun (pf: !ISEMP (n, l) >> ISEMP (n+1, l)):<prf> void
  } // end of [prval]
in
  // empty
end // end of [isemp_inc]

(* ****** ****** *)

extern fun{} isful_dec_fun {m,n:nat} {l:addr}
  (pf: !ISFUL (m,n,l) >> ISFUL (m,n-1,l) | m: int m, n: int n, p: ptr l):<1,~ref> void

implement{} isful_dec_fun {m,n} {l} (pf | m, n, p) = let
  prval pfstruct = queuearr_mut_struct_make () where {
    extern prfun queuearr_mut_struct_make
      ():<prf> queuearr_mut_struct (void, 0, 0, l) @ l
  } // end of [prval]
  // [pthread_cond_broadcast]: wake up all the waiting threads
  val () = if m = n then pthread_cond_broadcast (p->isful_cond)
  prval () = queuearr_mut_struct_free (pfstruct) where {
    extern prfun queuearr_mut_struct_free
      (_: queuearr_mut_struct (void, 0, 0, l) @ l):<prf> void
  } // end of [prval]
  prval () = isful_dec_prfun (pf) where {
    extern prfun isful_dec_prfun (pf: !ISFUL (m,n,l) >> ISFUL (m,n-1,l)):<prf> void
  } // end of [prval]
in
  // empty
end // end of [isful_inc]

(* ****** ****** *)

extern fun queuearr_lock_acquire {a:viewt@ype} {l:addr}
  (_: vbox (queuearr_lock_v (a, l)) | _: ptr l):<> (queuearr_lock_v (a, l) | void)
  = "queuearr_lock_acquire"

extern fun queuearr_lock_release {a:viewt@ype}
  {l:addr} (_: queuearr_lock_v (a, l) | _: ptr l):<> void
  = "queuearr_lock_release"

extern fun queuearr_lock_cond_wait_isemp {a:viewt@ype}
  {l:addr} (_: !queuearr_lock_v (a, l) | _: ptr l):<> void
  = "queuearr_lock_cond_wait_isemp"

extern fun queuearr_lock_cond_wait_isful {a:viewt@ype}
  {l:addr} (_: !queuearr_lock_v (a, l) | _: ptr l):<> void
  = "queuearr_lock_cond_wait_isful"

%{$

ats_void_type
queuearr_lock_acquire (ats_ptr_type p) {
  // fprintf (stderr, "queuearr_lock_acquire: start.\n") ;
  atslib_pthread_mutex_lock (&((queuearr_mut_struct*)p)->atslab_queue_mutex) ;
  // fprintf (stderr, "queuearr_lock_acquire: finish.\n") ;
  return ;
} // end of [queuearr_lock_acquire]

ats_void_type
queuearr_lock_release (ats_ptr_type p) {
  // fprintf (stderr, "queuearr_lock_release: start.\n") ;
  atslib_pthread_mutex_unlock (&((queuearr_mut_struct*)p)->atslab_queue_mutex) ;
  // fprintf (stderr, "queuearr_lock_release: finish.\n") ;
  return ;
} // end of [queuearr_lock_release]

ats_void_type
queuearr_lock_cond_wait_isemp (ats_ptr_type p0) {
  queuearr_mut_struct *p = (queuearr_mut_struct*)p0 ;
  atslib_pthread_cond_wait_mutex (&p->atslab_isemp_cond, &p->atslab_queue_mutex) ;
  return ;
} // end of [queuearr_lock_cond_wait_isemp]

ats_void_type
queuearr_lock_cond_wait_isful (ats_ptr_type p0) {
  queuearr_mut_struct *p = (queuearr_mut_struct*)p0 ;
  atslib_pthread_cond_wait_mutex (&p->atslab_isful_cond, &p->atslab_queue_mutex) ;
  return ;
} // end of [queuearr_lock_cond_wait_isful]

%}

(* ****** ****** *)

assume queuearr_mut_t (a:viewt@ype) =
  [l:addr] (vbox (queuearr_lock_v (a, l)) | ptr l)

(* ****** ****** *)

extern fun{a:viewt@ype}
queuearr_mut_make {m:nat} (m: int m):<> queuearr_mut_t (a)
// end of [queuearr_mut_make]

(* ****** ****** *)

extern fun{a:viewt@ype}
  queuearr_mut_enqueue (xs: queuearr_mut_t a, x: a):<1,~ref> void

implement{a} queuearr_mut_enqueue ([l:addr] q_mut, x) = let
  val (pfbox | p) = q_mut
  val (pflock | ()) = queuearr_lock_acquire {a} {l} (pfbox | p)
  val () = loop (pflock | p, x) where {
    fun loop
      (pflock: !queuearr_lock_v (a, l) | p: ptr l, x: a)
      :<1,~ref> void = let
      prval pf = queuearr_lock_v_unfold (pflock)
      val m = $LQA.linqueuearr_max (p->queue)
      val n = $LQA.linqueuearr_size (p->queue)
(*
      val () = $effmask_all begin
        prerr "queuearr_mut_enqueue: m = "; prerr m; prerr_newline ();
        prerr "queuearr_mut_enqueue: n = "; prerr n; prerr_newline ();
      end // end of [val]
*)
    in
      if m > n then let
        val () = $LQA.linqueuearr_enqueue (p->queue, x)
        val () = isemp_inc_fun (p->isemp_view | n, p)
        prval () = isful_inc_prfun (p->isful_view)
        prval () = pflock := queuearr_lock_v_fold (pf)
      in
        // empty
      end else let
        prval () = pflock := queuearr_lock_v_fold (pf)
        val () = queuearr_lock_cond_wait_isful (pflock | p)
      in
        loop (pflock | p, x)
      end // end of [if]
    end // end of [loop]
  } // end of [where]
in
  queuearr_lock_release {a} {l} (pflock | p)
end // end of [queuearr_mut_enqueue]

(* ****** ****** *)

extern fun{a:viewt@ype}
queuearr_mut_dequeue (xs: queuearr_mut_t a):<1,~ref> a
// end of [queuearr_mut_dequeue]

implement{a} queuearr_mut_dequeue ([l:addr] q_mut) = let
  val (pfbox | p) = q_mut
  val (pflock | ()) = queuearr_lock_acquire {a} {l} (pfbox | p)
  val x = loop (pflock | p) where {
    fun loop
      (pflock: !queuearr_lock_v (a, l) | p: ptr l):<1,~ref> a = let
      prval pf = queuearr_lock_v_unfold (pflock)
      val m = $LQA.linqueuearr_max (p->queue)
      val n = $LQA.linqueuearr_size (p->queue)
(*
      val () = $effmask_all begin
        prerr "queuearr_mut_dequeue: m = "; prerr m; prerr_newline ();
        prerr "queuearr_mut_dequeue: n = "; prerr n; prerr_newline ();
      end
*)
    in
      if n > 0 then let
        val x = $LQA.linqueuearr_dequeue (p->queue)
        prval () = isemp_dec_prfun (p->isemp_view)
        val () = isful_dec_fun (p->isful_view | m, n, p)
        prval () = pflock := queuearr_lock_v_fold (pf)
      in
        x // return value
      end else let
        prval () = pflock := queuearr_lock_v_fold (pf)
        val () = queuearr_lock_cond_wait_isemp (pflock | p)
      in
        loop (pflock | p)
      end // end of [if]
    end // end of [loop]
  } // end of [where]
in
  queuearr_lock_release {a} {l} (pflock | p); x
end // end of [queuearr_mut_dequeue]

(* ****** ****** *)

%{$

ats_ptr_type
queuearr_mut_make_lqa (ats_ptr_type lqa) {
  queuearr_mut_struct *p ;
  p = ATS_MALLOC (sizeof(queuearr_mut_struct)) ;
  p->atslab_queue = lqa ;
  pthread_mutex_init (&p->atslab_queue_mutex, NULL) ;
  pthread_cond_init (&p->atslab_isemp_cond, NULL) ;
  pthread_cond_init (&p->atslab_isful_cond, NULL) ;
  return p ;
} /* queuearr_mut_make */

%} // end of [%{$]

extern fun queuearr_mut_make_lqa {a:viewt@ype}
  {m:nat} (xs: $LQA.linqueuearr_vt (a, m, 0)):<> queuearr_mut_t a
  = "queuearr_mut_make_lqa"

(* ****** ****** *)

extern fun{a:viewt@ype}
queuearr_mut_make {m:pos} (m: int m):<> queuearr_mut_t a
// end of [queuearr_mul_make]

implement{a} queuearr_mut_make (m) = let
  val xs = $LQA.linqueuearr_make (m) in queuearr_mut_make_lqa (xs)
end // end of [queuearr_mut_make]

(* ****** ****** *)

(* end of [queuearr_mut.dats] *)
