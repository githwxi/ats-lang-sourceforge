(*

// some testing code for [linbinheap_ngc.dats]

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2009

*)

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"
staload Time = "libc/SATS/time.sats"

(* ****** ****** *)

staload H = "linbinheap_ngc.dats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/pointer.dats"

(* ****** ****** *)

typedef elt = int
viewtypedef heap_vt = $H.heap_vt (elt)

(* ****** ****** *)

#define N 100
implement main (argc, argv) = () where {
  var n: int = N
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end // end of [va]
  val [n:int] n = int1_of n
  val () = assert (n > 0)
(*
  val () = $Rand.srand48 (0L)
*)
  val () = $Rand.srand48_with_time ()
  val cmp = lam (x1: &elt, x2: &elt): Sgn =<cloref> compare_int_int (x1, x2)
  var heap: heap_vt = $H.linbinheap_empty ()
  var i: Nat // uninitialized
  val () = for (i := 0; i < n; i := i+1) let
    val elt = $Rand.randint n
    val (pf_gc, pf_at | p_at) = ptr_alloc<$H.btnode elt> ()
    prval () = __leak (pf_gc) where { extern prfun __leak {v:view} (pf: v): void }
    val () = p_at->elt := elt
    val () = $H.linbinheap_insert<elt> (pf_at | heap, p_at, cmp)
  in
    // nothing
  end // end of [val]
  val () = loop (sz, heap) where {
    val sz = $H.linbinheap_size<elt> (heap)
    fun loop {n:nat} .<n>. (
        sz: int n, heap: &heap_vt
      ) :<cloref1> void = let
      var x: elt? // uninitialized
    in
      if sz > 0 then let
        val (pfopt_at | p_at) = $H.linbinheap_delmin (heap, cmp)
        val () = assert (p_at <> null)
        prval Some_v pf_at = pfopt_at
        val () = print p_at->elt
        prval () = __leak (pf_at) where { extern prfun __leak {v:view} (pf: v): void }
        val () = print_newline ()
      in
        loop (sz-1, heap)
      end // end of [if]
    end // end of [loop]
  } // end of [loop]
  val tag = $H.linbinheap_empty_free (heap)
  val () = assert (~tag)
  prval () = opt_unnone {heap_vt} (heap)
} // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
