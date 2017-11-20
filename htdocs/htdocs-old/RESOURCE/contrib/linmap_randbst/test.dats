(*

// author: Hongwei Xi (October, 2008)

*)

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"
staload Time = "libc/SATS/time.sats"

(* ****** ****** *)

staload M = "linmap_randbst.dats"

(* ****** ****** *)

(*
** the efficiency gained from inlining the comparison
** function seems to be less than 5% (more like a 3%)
*)

(*
implement $M.compare_key_key<int> (x1, x2, cmp) =
  if x1 < x2 then ~1 else if x1 > x2 then 1 else 0
*)

implement main (argc, argv) = let
  val () = gc_chunk_count_limit_max_set (~1) // infinite
  var n: int = 0
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end
  val [n:int] n = int1_of n
  val () = assert (n > 0)
// (*
  val () = $Rand.srand48 (0L)
  // val () = $Rand.srand48_with_time ()
// *)
  fn cmp (x1: int, x2: int):<cloref> Sgn = compare (x1, x2)

  var map: $M.map_vt (int, string) = $M.linmap_empty ()
  var i: int; val () = for (i := 0; i < n; i := i+1) let
    val key = $Rand.randint n
    val itm = tostring key // val itm = sprintf ("%i", @(key))
    // val () = printf ("key = %i and itm = %s\n", @(key, itm))
    val ans = $M.linmap_insert<int,string> (map, key, itm, cmp)
  in
    case+ ans of ~Some_vt _ => () | ~None_vt () => ()
  end // end [for]
  val size = $M.linmap_size (map)
  val () = begin
    print "size = "; print size; print_newline ()
  end // end of [val]
  val height = $M.linmap_height (map)
  val () = begin
    print "height = "; print height; print_newline ()
  end // end of [val]
  val () = if n < 100 then let
    prval pf = unit_v (); val () =
      $M.linmap_foreach_clo<int,string> {unit_v} (pf | map, !p_clo) where {
      var !p_clo = @lam (pf: !unit_v | k: int, i: &string): void =<clo> $effmask_all
        (printf ("%i\t->\t%s\n", @(k, i)))
    } // end of [val]
    prval unit_v () = pf
  in
    // empty
  end // end of [val]
//
  val k0 = 0
  val () = printf ("%i\t->\t", @(k0))
  val () = case+ $M.linmap_search (map, k0, cmp) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k1 = 1
  val () = printf ("%i\t->\t", @(k1))
  val () = case+ $M.linmap_search (map, k1, cmp) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k10 = 10
  val () = printf ("%i\t->\t", @(k10))
  val () = case+ $M.linmap_search (map, k10, cmp) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k100 = 100
  val () = printf ("%i\t->\t", @(k100))
  val () = case+ $M.linmap_search (map, k100, cmp) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k1000 = 1000
  val () = printf ("%i\t->\t", @(k1000))
  val () = case+ $M.linmap_search (map, k1000, cmp) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k10000 = 10000
  val () = printf ("%i\t->\t", @(k10000))
  val () = case+ $M.linmap_search (map, k10000, cmp) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
//
  var i: int (* uninitialized *)
  val () = for (i := 0; i < n; i := i+1) let
    val key = i
    val ans =
      $M.linmap_remove<int,string> (map, i, cmp)
    val () = (case+ ans of
      | ~Some_vt _ => () | ~None_vt () => ()
    ) : void// end of [val]
  in
    // nothing
  end // end of [for]
//
  val map = map
  val () = assert ($M.linmap_empty_free (map) = false)
  prval () = opt_unnone (map)
//
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
