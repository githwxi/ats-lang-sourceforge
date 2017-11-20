(*
**
** An implementation of persistent queues based on arrays
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

staload _ = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload LQA = "linqueuearr.dats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

abstype queuearr_ref_t (a:viewt@ype)

(* ****** ****** *)

viewtypedef linqueuearr_vt (a:viewt@ype) =
  [m,n:nat | n <= m] $LQA.linqueuearr_vt (a, m, n)

assume queuearr_ref_t (a:viewt@ype) = ref (linqueuearr_vt (a))

(* ****** ****** *)

extern fun{a:viewt@ype}
  queuearr_ref_make {m:nat} (m: int m): queuearr_ref_t (a)

implement{a} queuearr_ref_make (m) =
  ref_make_elt ($LQA.linqueuearr_make<a> (m))

(* ****** ****** *)

extern fun{a:viewt@ype}
  queuearr_ref_enqueue (xs: queuearr_ref_t a, x: a):<!ref> Option_vt a

extern fun{a:viewt@ype}
  queuearr_ref_enqueue_exn (xs: queuearr_ref_t a, x: a):<!ref> void

exception {a:viewt@ype} EnqueueException of a

implement{a} queuearr_ref_enqueue (r, x) = let
  val (vbox pf | p) = ref_get_view_ptr (r)
  val xs = !p
  val isfull = $LQA.linqueuearr_isfull (xs)
in
  if isfull then begin
    !p := xs; Some_vt (x)
  end else let
    val () = $LQA.linqueuearr_enqueue (xs, x) in (!p := xs; None_vt ())
  end // end of [if]
end // end of [queuearr_ref_enqueue]

implement{a} queuearr_ref_enqueue_exn (r, x) = let
  val ans = queuearr_ref_enqueue (r, x)
in
  case+ ans of 
  | ~Some_vt (x) => $raise EnqueueException (x) | ~None_vt () => ()
end // end of [queuearr_ref_enqueue_exn]

(* ****** ****** *)

extern fun{a:viewt@ype}
  queuearr_ref_dequeue (xs: queuearr_ref_t a):<!ref> Option_vt a

extern fun{a:viewt@ype}
  queuearr_ref_dequeue_exn (xs: queuearr_ref_t a):<!ref> a

exception DequeueException of ()

implement{a} queuearr_ref_dequeue (r) = let
  val (vbox pf | p) = ref_get_view_ptr (r)
  val xs = !p; val n = $LQA.linqueuearr_size (xs)
in
  if n > 0 then let
    val x = $LQA.linqueuearr_dequeue (xs) in (!p := xs; Some_vt x)
  end else begin
    !p := xs; None_vt ()
  end // end of [if]
end // end of [queuearr_ref_dequeue]

implement{a} queuearr_ref_dequeue_exn (r) = let
  val ans = queuearr_ref_dequeue (r)
in
  case+ ans of 
  | ~Some_vt (x) => x | ~None_vt () => $raise DequeueException ()
end // end of [queuearr_ref_dequeue_exn]

(* ****** ****** *)

(* end of [queuearr_ref.dats] *)
