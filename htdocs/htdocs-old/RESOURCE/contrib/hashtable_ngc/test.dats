(*

// author: Hongwei Xi (August, 2009)

*)

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"
staload Time = "libc/SATS/time.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload H = "hashtable_ngc.dats"

(* ****** ****** *)

staload FREELST = "libats/SATS/freelst.sats"
staload _(*anonymous*) = "libats/DATS/freelst.dats"

typedef freeitm_t (a:viewt@ype, l:addr) = $FREELST.freeitm_t (a, l)

viewtypedef bucket = $H.bucket (int, string)
viewtypedef bucketlst = [l:addr] ($FREELST.freelst_v (bucket, l) | ptr l)

val () = assert (sizeof<bucket> >= sizeof<ptr>)

(* ****** ****** *)

val () = assert (sizeof<bucket> >= sizeof<ptr>)

var the_bucketlst_ref
  : bucketlst = @($FREELST.freelst_v_nil () | null)
// end of [var]

val (pfbox_the_bucketlst | ()) =
  vbox_make_view_ptr {bucketlst} (view@ the_bucketlst_ref | &the_bucketlst_ref)
// end of [val]

extern fun bucket_ptr_alloc ()
  :<!ref> [l:addr | l <> null] (bucket? @ l | ptr l)

#define BUCKET_BLOCK_SIZE (0x1000) // 2^12 = 4096

implement bucket_ptr_alloc () = let
  prval vbox pf_the_bucketlst = pfbox_the_bucketlst
  val p_lst = the_bucketlst_ref.1
in
  if p_lst <> null then let
    val (pf_at | p1_lst) =
      $FREELST.freelst_uncons {bucket} (the_bucketlst_ref.0 | p_lst)
    val () = the_bucketlst_ref.1 := p1_lst
(*
    val () = $effmask_all begin
      prerr "bucket_ptr_alloc: p_lst = "; prerr p_lst; prerr_newline ()
    end // end of [val]
*)
  in
    #[.. | (pf_at | p_lst)]
  end else let
(*
**  NOTE: using [malloc_gc] may result in the allocated bytes being reclaimed!!!
*)
    val (pf_ngc, pf_arr | p_arr) = malloc_ngc (BUCKET_BLOCK_SIZE)
    prval () = __leak (pf_ngc) where { extern prfun __leak {v:view} (pf: v): void }
    val p_lst = $FREELST.freelst_add_bytes_tsz {bucket}
      (the_bucketlst_ref.0, pf_arr | p_lst, p_arr, BUCKET_BLOCK_SIZE, sizeof<bucket>)
    val () = $effmask_exn (assert (p_lst <> null))
    val (pf_at | p1_lst) = $FREELST.freelst_uncons {bucket} (the_bucketlst_ref.0 | p_lst)
    val () = the_bucketlst_ref.1 := p1_lst
(*
    val () = $effmask_all begin
      prerr "bucket_ptr_alloc: p_lst = "; prerr p_lst; prerr_newline ()
    end // end of [val]
*)
  in
    #[.. | (pf_at | p_lst)]
  end // end of [if]
end (* end of [bucket_ptr_alloc] *)

extern fun bucket_ptr_free {l:addr} (pf: bucket @ l | p: ptr l):<!ref> void

implement bucket_ptr_free (pf | p) = let
(*
  val () = $effmask_all begin
    prerr "bucket_ptr_free: p = "; prerr p; prerr_newline ()
  end // end of [val]
*)
  prval vbox pf_the_bucketlst = pfbox_the_bucketlst
  val () = $FREELST.freelst_cons {bucket}
    (pf, the_bucketlst_ref.0 | p, the_bucketlst_ref.1)
  val () = the_bucketlst_ref.1 := p
in
  // nothing
end // end of [bucket_ptr_free]

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
  val () = (if argc >= 2 then n := int_of_string (argv.[1]))
  val [N:int] N = int1_of n
  val () = assert (N > 0)
(*
  val () = $Rand.srand48_with_time ()
*)
  fn hash (x: int):<cloref> ulint = ulint_of_int (x)
  fn eq (x1: int, x2: int):<cloref> bool = (x1 = x2)

  val sz = size1_of_int1 (N)
  val (pf_gc, pf_arr | p_arr) = array_ptr_alloc_tsz {ptr} (sz, sizeof<ptr>)
  prval () = free_gc_elim (pf_gc)
//
  typedef key = int; viewtypedef itm = string
//
  var tbl: $H.hashtbl_vt (key, itm, N) = $H.hashtbl_make (pf_arr | p_arr, sz)
  var i: int // uninitialized
  val () = for (i := 0; i < n; i := i+1) let
    val key = $Rand.randint N
    val itm = tostring key // val itm = sprintf ("%i", @(key))
    // val () = printf ("key = %i and itm = %s\n", @(key, itm))
    val (pf_at | p) = bucket_ptr_alloc ()
    val () = p->key := key and () = p->itm := itm
  in
    $H.hashtbl_insert<key,itm> (pf_at | tbl, sz, p, hash, eq)
  end (* end [for] *)
//
  var res: itm? // uninitialized
//
  val k0 = 0
  val () = printf ("%i\t->\t", @(k0))
  val tag = $H.hashtbl_search<key,itm>(tbl, sz, k0, res, hash, eq)
  val () = if :(res: itm?) => tag > 0 then let
    prval () = opt_unsome {itm} (res)
  in
    print "Some("; print res; print ")"
  end else let
    prval () = opt_unnone {itm} (res)
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
//
  val k1 = 1
  val () = printf ("%i\t->\t", @(k1))
  val tag = $H.hashtbl_search<key,itm>(tbl, sz, k1, res, hash, eq)
  val () = if :(res: itm?) => tag > 0 then let
    prval () = opt_unsome {itm} (res)
  in
    print "Some("; print res; print ")"
  end else let
    prval () = opt_unnone {itm} (res)
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
//
  val k10 = 10
  val () = printf ("%i\t->\t", @(k10))
  val tag = $H.hashtbl_search<key,itm>(tbl, sz, k10, res, hash, eq)
  val () = if :(res: itm?) => tag > 0 then let
    prval () = opt_unsome {itm} (res)
  in
    print "Some("; print res; print ")"
  end else let
    prval () = opt_unnone {itm} (res)
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
//
  val k100 = 100
  val () = printf ("%i\t->\t", @(k100))
  val tag = $H.hashtbl_search<key,itm>(tbl, sz, k100, res, hash, eq)
  val () = if :(res: itm?) => tag > 0 then let
    prval () = opt_unsome {itm} (res)
  in
    print "Some("; print res; print ")"
  end else let
    prval () = opt_unnone {itm} (res)
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
//
  val k1000 = 1000
  val () = printf ("%i\t->\t", @(k1000))
  val tag = $H.hashtbl_search<key,itm>(tbl, sz, k1000, res, hash, eq)
  val () = if :(res: itm?) => tag > 0 then let
    prval () = opt_unsome {itm} (res)
  in
    print "Some("; print res; print ")"
  end else let
    prval () = opt_unnone {itm} (res)
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
//
  val k10000 = 10000
  val () = printf ("%i\t->\t", @(k10000))
  val tag = $H.hashtbl_search<key,itm>(tbl, sz, k10000, res, hash, eq)
  val () = if :(res: itm?) => tag > 0 then let
    prval () = opt_unsome {itm} (res)
  in
    print "Some("; print res; print ")"
  end else let
    prval () = opt_unnone {itm} (res)
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
//
  val _(*ptr*) = __cast (tbl) where {
    extern castfn __cast {sz:pos} (tbl: $H.hashtbl_vt (key, itm, sz)): ptr
  } // end of [val]
//
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
