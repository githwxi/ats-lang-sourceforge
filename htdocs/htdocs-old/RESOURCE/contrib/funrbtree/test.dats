(*

// author: Hongwei Xi (October, 2008)

*)

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"
staload Time = "libc/SATS/time.sats"

(* ****** ****** *)

staload S = "funrbtree.dats"

(* ****** ****** *)

// dynload "funrbtree.dats"

(* ****** ****** *)

(*
** the efficiency gained from inlining the comparison
** function seems to be less than 5% (more like a 3%)
*)

(*
implement $S.compare_elt_elt<int> (x1, x2, cmp) =
  if x1 < x2 then ~1 else if x1 > x2 then 1 else 0
*)

implement $S.print_elt<int> (x) = print_int (x)

implement main (argc, argv) = let
  val () = gc_chunk_count_limit_max_set (~1) // infinite
  var n: int = 0
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end
  val [n:int] n = int1_of n
  val () = assert (n > 0)
(*
  // val () = $Rand.srand48 (0L)
  // val () = $Rand.srand48_with_time ()
*)
  fn cmp (x1: int, x2: int):<cloref> Sgn = compare (x1, x2)

  var set: $S.set_t (int) = $S.rbtree_nil ()
  var i: int; val () = for (i := 0; i < n; i := i+1) let
    var tag: int // uninitialized
    val elt = $Rand.randint n
    // val () = printf ("elt = %i\n", @(elt))
  in
    set := $S.rbtree_insert<int> (set, elt, tag, cmp)
  end // end [for]
//
  val size = $S.rbtree_size (set)
  val () = begin
    print "size = "; print size; print_newline ()
  end // end of [val]
//
  val bheight = $S.rbtree_black_height (set)
  val () = begin
    print "black height = "; print bheight; print_newline ()
  end // end of [val]
//
  val () = begin
    print "set =\n"; $S.print_rbtree<int> (set)
  end // end of [val]
//
  var i: int; val () = for (i := 0; i < n/2; i := i+1) let
    var tag: int // uninitialized
    val elt = 2 * i
    // val () = printf ("elt = %i\n", @(elt))
  in
    set := $S.rbtree_remove<int> (set, elt, tag, cmp)
  end // end [for]
//
  val size = $S.rbtree_size (set)
  val () = begin
    print "size = "; print size; print_newline ()
  end // end of [val]
//
  val () = begin
    print "set (after all even numbers are removed) =\n"; $S.print_rbtree<int> (set)
  end // end of [val]
//
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
