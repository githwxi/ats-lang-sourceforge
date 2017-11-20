(*

// author: Hongwei Xi (August, 2009)

*)

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"
staload Time = "libc/SATS/time.sats"

(* ****** ****** *)

staload M = "linmap_rbtree_ngc.dats"

(* ****** ****** *)

staload FREELST = "libats/SATS/freelst.sats"
staload _(*anonymous*) = "libats/DATS/freelst.dats"

typedef freeitm_t (a:viewt@ype, l:addr) = $FREELST.freeitm_t (a, l)

viewtypedef rbnode = $M.rbnode (int, string)
viewtypedef rbnodelst = [l:addr] ($FREELST.freelst_v (rbnode, l) | ptr l)

val () = assert (sizeof<rbnode> >= sizeof<ptr>)

var the_rbnodelst_ref
  : rbnodelst = @($FREELST.freelst_v_nil () | null)
// end of [var]

val (pfbox_the_rbnodelst | ()) =
  vbox_make_view_ptr {rbnodelst} (view@ the_rbnodelst_ref | &the_rbnodelst_ref)
// end of [val]

extern fun rbnode_ptr_alloc ()
  :<!ref> [l:addr | l <> null] (rbnode? @ l | ptr l)

#define AVLNODE_BLOCK_SIZE (0x1000) // 2^12 = 4096

implement rbnode_ptr_alloc () = let
  prval vbox pf_the_rbnodelst = pfbox_the_rbnodelst
  val p_lst = the_rbnodelst_ref.1
in
  if p_lst <> null then let
    val (pf_at | p1_lst) =
      $FREELST.freelst_uncons {rbnode} (the_rbnodelst_ref.0 | p_lst)
    val () = the_rbnodelst_ref.1 := p1_lst
(*
    val () = $effmask_all begin
      prerr "rbnode_ptr_alloc: p_lst = "; prerr p_lst; prerr_newline ()
    end // end of [val]
*)
  in
    #[.. | (pf_at | p_lst)]
  end else let
(*
**  NOTE: using [malloc_gc] may result in the allocated bytes being reclaimed!!!
*)
    val (pf_ngc, pf_arr | p_arr) = malloc_ngc (AVLNODE_BLOCK_SIZE)
    prval () = __leak (pf_ngc) where { extern prfun __leak {v:view} (pf: v): void }
    val p_lst = $FREELST.freelst_add_bytes_tsz {rbnode}
      (the_rbnodelst_ref.0, pf_arr | p_lst, p_arr, AVLNODE_BLOCK_SIZE, sizeof<rbnode>)
    val () = $effmask_exn (assert (p_lst <> null))
    val (pf_at | p1_lst) = $FREELST.freelst_uncons {rbnode} (the_rbnodelst_ref.0 | p_lst)
    val () = the_rbnodelst_ref.1 := p1_lst
(*
    val () = $effmask_all begin
      prerr "rbnode_ptr_alloc: p_lst = "; prerr p_lst; prerr_newline ()
    end // end of [val]
*)
  in
    #[.. | (pf_at | p_lst)]
  end // end of [if]
end (* end of [rbnode_ptr_alloc] *)

extern fun rbnode_ptr_free {l:addr} (pf: rbnode @ l | p: ptr l):<!ref> void

implement rbnode_ptr_free (pf | p) = let
(*
  val () = $effmask_all begin
    prerr "rbnode_ptr_free: p = "; prerr p; prerr_newline ()
  end // end of [val]
*)
  prval vbox pf_the_rbnodelst = pfbox_the_rbnodelst
  val () = $FREELST.freelst_cons {rbnode}
    (pf, the_rbnodelst_ref.0 | p, the_rbnodelst_ref.1)
  val () = the_rbnodelst_ref.1 := p
in
  // nothing
end // end of [rbnode_ptr_free]

(* ****** ****** *)

(*

sortdef clr = $M.clr

#define N 10
implement $M.print_rbtree<int,string> (pf | p) = let
  stadef rbtree_v = $M.rbtree_v
  fun indent (n: int): void = if n > 0 then (print ' '; indent (n-1)) else ()
  // end of [indent]
  fun loop {c:clr} {bh:nat} {v:nat} {pnt,slf:addr} .<bh,c+v>.
    (pf: !rbtree_v (int,string,c,bh,v,pnt,slf) | n: int, p: ptr slf): void =
    if p <> null then let
      prval $M.B (pf_clr, pf_at, pf_l, pf_r) = pf
      prval () = $M.clr_lemma (pf_clr)
      val () = loop (pf_l | n+1, p->left)
      val () = (indent (N-n); print p->key; print_newline ())
      val () = loop (pf_r | n+1, p->right)
      prval () = pf := $M.B (pf_clr, pf_at, pf_l, pf_r)
    in
      // nothing
    end // end of [if]
  // end of [loop]
in
  loop (pf | 0, p)
end (* end of [print_rbtree] *)

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
    val key = $Rand.randint n
    val itm = tostring key // val itm = sprintf ("%i", @(key))
    // val () = printf ("key = %i and itm = %s\n", @(key, itm))
    val (pf_at | p) = rbnode_ptr_alloc ()
    val () = p->key := key and () = p->itm := itm
    val tag = $M.linmap_insert<int,string> (pf_at | map, p, cmp)
//
    // val () = $effmask_all ($M.print_linmap (map))
//
  in
    if tag = 0 then let
      prval None_v () = pf_at in
    end else let
      prval Some_v pf_at = pf_at in rbnode_ptr_free (pf_at | p)
    end // end of [if]
  end (* end [for] *)
  val size = $M.linmap_size (map)
  val () = begin
    print "size = "; print size; print_newline ()
  end // end of [val]
  val height = $M.linmap_black_height (map)
  val () = begin
    print "height = "; print height; print_newline ()
  end // end of [val]
//
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
      prval Some_v pf_at = pf_at; val () = rbnode_ptr_free (pf_at | p_at)
    in
      // nothing
    end else let
      prval None_v () = pf_at in ()
    end // end of [if]
  in
    // nothing
  end // end of [for]
//
  val map = map
//
  val size = $M.linmap_size (map)
  val () = begin
    print "size = "; print size; print_newline ()
  end // end of [val]
  val height = $M.linmap_black_height (map)
  val () = begin
    print "height = "; print height; print_newline ()
  end // end of [val]
//
  val () = assert ($M.linmap_empty_free (map) = 0)
  prval () = opt_unnone (map)
//
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
