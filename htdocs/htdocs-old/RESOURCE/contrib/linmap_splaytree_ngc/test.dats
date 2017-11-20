(*

// author: Hongwei Xi (August, 2009)

*)

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"
staload Time = "libc/SATS/time.sats"

(* ****** ****** *)

staload M = "linmap_splaytree_ngc.dats"

(* ****** ****** *)

staload FREELST = "libats/SATS/freelst.sats"
staload _(*anonymous*) = "libats/DATS/freelst.dats"

typedef freeitm_t (a:viewt@ype, l:addr) = $FREELST.freeitm_t (a, l)

viewtypedef node = $M.node (int, string)
viewtypedef nodelst = [l:addr] ($FREELST.freelst_v (node, l) | ptr l)

val () = assert (sizeof<node> >= sizeof<ptr>)

var the_nodelst_ref
  : nodelst = @($FREELST.freelst_v_nil () | null)
// end of [var]

val (pfbox_the_nodelst | ()) =
  vbox_make_view_ptr {nodelst} (view@ the_nodelst_ref | &the_nodelst_ref)
// end of [val]

extern fun node_ptr_alloc ()
  :<!ref> [l:addr | l <> null] (node? @ l | ptr l)

#define NODE_BLOCK_SIZE (0x1000) // 2^12 = 4096

implement node_ptr_alloc () = let
  prval vbox pf_the_nodelst = pfbox_the_nodelst
  val p_lst = the_nodelst_ref.1
in
  if p_lst <> null then let
    val (pf_at | p1_lst) =
      $FREELST.freelst_uncons {node} (the_nodelst_ref.0 | p_lst)
    val () = the_nodelst_ref.1 := p1_lst
(*
    val () = $effmask_all begin
      prerr "node_ptr_alloc: p_lst = "; prerr p_lst; prerr_newline ()
    end // end of [val]
*)
  in
    #[.. | (pf_at | p_lst)]
  end else let
(*
**  NOTE: using [malloc_gc] may result in the allocated bytes being reclaimed!!!
*)
    val (pf_ngc, pf_arr | p_arr) = malloc_ngc (NODE_BLOCK_SIZE)
    prval () = __leak (pf_ngc) where { extern prfun __leak {v:view} (pf: v): void }
    val p_lst = $FREELST.freelst_add_bytes_tsz {node}
      (the_nodelst_ref.0, pf_arr | p_lst, p_arr, NODE_BLOCK_SIZE, sizeof<node>)
    val () = $effmask_exn (assert (p_lst <> null))
    val (pf_at | p1_lst) = $FREELST.freelst_uncons {node} (the_nodelst_ref.0 | p_lst)
    val () = the_nodelst_ref.1 := p1_lst
(*
    val () = $effmask_all begin
      prerr "node_ptr_alloc: p_lst = "; prerr p_lst; prerr_newline ()
    end // end of [val]
*)
  in
    #[.. | (pf_at | p_lst)]
  end // end of [if]
end (* end of [node_ptr_alloc] *)

extern fun node_ptr_free {l:addr} (pf: node @ l | p: ptr l):<!ref> void

implement node_ptr_free (pf | p) = let
(*
  val () = $effmask_all begin
    prerr "node_ptr_free: p = "; prerr p; prerr_newline ()
  end // end of [val]
*)
  prval vbox pf_the_nodelst = pfbox_the_nodelst
  val () = $FREELST.freelst_cons {node}
    (pf, the_nodelst_ref.0 | p, the_nodelst_ref.1)
  val () = the_nodelst_ref.1 := p
in
  // nothing
end // end of [node_ptr_free]

(* ****** ****** *)

(*

implement $M.print_tree<int,string> (pf | p) = let
  stadef tree_v = $M.tree_v
  fun indent {n:nat} .<n>.
    (n: int n): void = if n > 0 then (print ' '; indent (n-1)) else ()
  // end of [indent]
  fun loop {h:nat} {pnt,slf:addr} .<h>.
    (pf: !tree_v (int,string,h,pnt,slf) | p: ptr slf): void =
  if p <> null then let
    prval $M.B (pf_at, pf_l, pf_r) = pf
    val () = loop (pf_l | p->left)
    val () = (indent p->height; print_int (p->key); print_newline ())
    val () = loop (pf_r | p->right)
    prval () = pf := $M.B (pf_at, pf_l, pf_r)
  in
    // nothing
  end // end of [val]
in
  loop (pf | p)
end (* end of [print_tree] *)

*)

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

  typedef key = int and itm = string
  var map: $M.map_vt (key, itm) = $M.linmap_empty ()
  var i: int (* uninitialized *)
  val () = for (i := 0; i < n; i := i+1) let
    // val key = i
    val key = $Rand.randint n
    val itm = tostring key // val itm = sprintf ("%i", @(key))
    // val () = printf ("key = %i and itm = %s\n", @(key, itm))
    val (pf_at | p) = node_ptr_alloc ()
    val () = p->key := key and () = p->itm := itm
    val tag = $M.linmap_insert<int,string> (pf_at | map, p, cmp)
//
    // val () = $effmask_all ($M.print_linmap (map))
//
  in
    if tag = 0 then let
      prval None_v () = pf_at in
    end else let
      prval Some_v pf_at = pf_at in node_ptr_free (pf_at | p)
    end // end of [if]
  end (* end [for] *)
// (*
  val size = $M.linmap_size (map)
  val () = begin
    print "size = "; print size; print_newline ()
  end // end of [val]
  val height = $M.linmap_height (map)
  val () = begin
    print "height = "; print height; print_newline ()
  end // end of [val]
// *)
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
  var res: string with pf_res // uninitialized
  val k0 = 0
  val () = printf ("%i\t->\t", @(k0))
  val tag = $M.linmap_search<key,itm>(pf_res | map, k0, &res, cmp)
  val () = if :(pf_res: string? @ res) => tag > 0 then let
    prval InsRight_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "Some("; print res; print ")"
  end else let
    prval InsLeft_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
  val k1 = 1
  val () = printf ("%i\t->\t", @(k1))
  val tag = $M.linmap_search<key,itm> (pf_res | map, k1, &res, cmp)
  val () = if :(pf_res: string? @ res) => tag > 0 then let
    prval InsRight_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "Some("; print res; print ")"
  end else let
    prval InsLeft_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
  val k10 = 10
  val () = printf ("%i\t->\t", @(k10))
  val tag = $M.linmap_search<key,itm> (pf_res | map, k10, &res, cmp)
  val () = if :(pf_res: string? @ res) => tag > 0 then let
    prval InsRight_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "Some("; print res; print ")"
  end else let
    prval InsLeft_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
  val k100 = 100
  val () = printf ("%i\t->\t", @(k100))
  val tag = $M.linmap_search<key,itm> (pf_res | map, k100, &res, cmp)
  val () = if :(pf_res: string? @ res) => tag > 0 then let
    prval InsRight_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "Some("; print res; print ")"
  end else let
    prval InsLeft_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
  val k1000 = 1000
  val () = printf ("%i\t->\t", @(k1000))
  val tag = $M.linmap_search<key,itm> (pf_res | map, k1000, &res, cmp)
  val () = if :(pf_res: string? @ res) => tag > 0 then let
    prval InsRight_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "Some("; print res; print ")"
  end else let
    prval InsLeft_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
  val k10000 = 10000
  val () = printf ("%i\t->\t", @(k10000))
  val tag = $M.linmap_search<key,itm> (pf_res | map, k10000, &res, cmp)
  val () = if :(pf_res: string? @ res) => tag > 0 then let
    prval InsRight_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "Some("; print res; print ")"
  end else let
    prval InsLeft_v pf1_res = pf_res; prval () = pf_res := pf1_res
  in
    print "None()"
  end // end of [val]
  val () = print_newline ()
//
  var i: int (* uninitialized *)
  val () = for (i := 0; i < n; i := i+1) let
    val key = i
    val (pf_at | p_at) =
      $M.linmap_remove<int,string> (map, i, cmp)
    val () = if p_at <> null then let
      prval Some_v pf_at = pf_at; val () = node_ptr_free (pf_at | p_at)
    in
      // nothing
    end else let
      prval None_v () = pf_at in ()
    end // end of [if]
  in
    // nothing
  end // end of [for]
//
  val size = $M.linmap_size (map)
  val () = begin
    print "size = "; print size; print_newline ()
  end // end of [val]
  val height = $M.linmap_height (map)
  val () = begin
    print "height = "; print height; print_newline ()
  end // end of [val]
//
  val map = map
  val () = assert ($M.linmap_empty_free (map) = 0)
  prval () = opt_unnone (map)
//
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
