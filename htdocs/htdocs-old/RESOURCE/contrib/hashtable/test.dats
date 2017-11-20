(*

// author: Hongwei Xi (October, 2008)

*)

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"
staload Time = "libc/SATS/time.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload H = "hashtable.dats"

(* ****** ****** *)

// dynload "hashtable.dats" // not needed as [ATS_DYNLOADFLAG = 0]

(* ****** ****** *)

(*
** the efficiency gained from inlining the comparison
** function seems to be less than 5% (more like a 3%)
*)

// (*
implement $H.hash_key<int> (x, _) = ulint_of_int (x)
implement $H.equal_key_key<int> (x1, x2, _) = (x1 = x2)
// *)

implement main (argc, argv) = let
  val () = gc_chunk_count_limit_max_set (~1) // infinite
  var n: int = 0
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end
  val [n:int] n = int1_of n
  val () = assert (n > 0)
(*
  val () = $Rand.srand48_with_time ()
*)
  fn hash (x: int):<cloref> ulint = ulint_of_int (x)
  fn eq (x1: int, x2: int):<cloref> bool = (x1 = x2)

  var tbl: $H.hashtbl_t (int, string) = $H.hashtbl_make (hash, eq)
  var i: int; val () = for (i := 0; i < n; i := i+1) let
    val key = $Rand.randint n
    val itm = tostring key // val itm = sprintf ("%i", @(key))
    // val () = printf ("key = %i and itm = %s\n", @(key, itm))
    val ans = $H.hashtbl_insert_err<int,string> (tbl, key, itm)
  in
    case+ ans of ~Some_vt _ => () | ~None_vt () => ()
  end // end [while]
  val size = $H.hashtbl_size (tbl)
  val () = begin
    print "size = "; print size; print_newline ()
  end
  val total = $H.hashtbl_total (tbl)
  val () = begin
    print "total = "; print total; print_newline ()
  end
  val k0 = 0
  val () = printf ("%i\t->\t", @(k0))
  val () = case+ $H.hashtbl_search (tbl, k0) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k1 = 1
  val () = printf ("%i\t->\t", @(k1))
  val () = case+ $H.hashtbl_search (tbl, k1) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k10 = 10
  val () = printf ("%i\t->\t", @(k10))
  val () = case+ $H.hashtbl_search (tbl, k10) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k100 = 100
  val () = printf ("%i\t->\t", @(k100))
  val () = case+ $H.hashtbl_search (tbl, k100) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k1000 = 1000
  val () = printf ("%i\t->\t", @(k1000))
  val () = case+ $H.hashtbl_search (tbl, k1000) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k10000 = 10000
  val () = printf ("%i\t->\t", @(k10000))
  val () = case+ $H.hashtbl_search (tbl, k10000) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
