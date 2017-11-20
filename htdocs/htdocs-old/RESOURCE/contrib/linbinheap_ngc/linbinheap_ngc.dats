(*
**
** An implementation of linear binary heaps based on Braun trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: September, 2009
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

absviewtype heap_vt (elt:viewt@ype+) // boxed viewtype

(* ****** ****** *)

sortdef vt0p = viewt@ype

(* ****** ****** *)

typedef cmp (elt:vt0p) = (&elt, &elt) -<cloref> Sgn

extern fun{elt:vt0p}
  compare_elt_elt (x1: &elt, x2: &elt, cmp: cmp elt):<> Sgn
// end of ...

implement{elt} compare_elt_elt (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

extern fun{}
linbinheap_empty {elt:vt0p} ():<> heap_vt (elt)

extern fun{}
linbinheap_empty_free {elt:vt0p}
  (hp: !heap_vt (elt) >> opt (heap_vt (elt), tag)): #[tag:bool] bool tag
// end of [linbinheap_empty_free]

(* ****** ****** *)

extern fun{}
linbinheap_is_empty {elt:vt0p} (hp: !heap_vt elt):<> bool

extern fun{}
linbinheap_isnot_empty {elt:vt0p} (hp: !heap_vt elt):<> bool

(* ****** ****** *)

// [linbinheap_size] is of O(log^2 n) time-complexity
extern fun{elt:vt0p} linbinheap_size (hp: !heap_vt elt):<> Nat
// end of ...

// absviewt@ype{a:viewt@ype} btnode // this is not yet supported ...

viewtypedef btnode (
  a:viewt@ype, lft:addr, rgh:addr
) = @{
  elt= a, lft= ptr lft, rgh= ptr rgh
} // end of [btnode]

viewtypedef btnode (a:viewt@ype) = @{ elt= a, lft= ptr?, rgh= ptr? }

(* ****** ****** *)

extern fun{elt:vt0p} linbinheap_insert {l_at:addr}
  (pf_at: btnode elt @ l_at | hp: &heap_vt elt, p_at: ptr l_at, cmp: cmp elt):<> void
// end of ...

extern fun{elt:vt0p}
  linbinheap_delmin (hp: &heap_vt elt, cmp: cmp elt)
  :<> [l_at:addr] (ptropt_v (btnode elt, l_at) | ptr l_at)
// end of ...

(* ****** ****** *)

dataview brauntree_v (
  a:viewt@ype+(*elt*), int(*size*), addr(*root*)
) =
  | {n1,n2:nat | n2 <= n1; n1 <= n2+1} {lft,rgh:addr} {slf:addr | slf <> null}
    B (a, n1+n2+1, slf) of (
      btnode (a, lft, rgh) @ slf, brauntree_v (a, n1, lft), brauntree_v (a, n2, rgh)
    ) // end of [B]
  | E (a, 0, null) of ()
// end of [brauntree_v]

stadef bt_v = brauntree_v

(* ****** ****** *)

assume heap_vt (elt:vt0p) =
  [n:nat;slf:addr] (brauntree_v (elt, n, slf) | ptr slf)
// end of [heap_vt]

(* ****** ****** *)

implement{} linbinheap_empty () = (E () | null)
implement{} linbinheap_empty_free {elt} (hp) = let
  viewtypedef heap_vt = heap_vt elt
in
  if hp.1 <> null then let
    prval () = opt_some {heap_vt} (hp) in true
  end else let
    prval E () = hp.0; prval () = opt_none {heap_vt} (hp) in false
  end (* end of [if] *)
end (* end of [linbinheap_empty_free] *)

(* ****** ****** *)

implement{} linbinheap_is_empty (hp) = (hp.1 = null)
implement{} linbinheap_isnot_empty (hp) = (hp.1 <> null)

(* ****** ****** *)

implement{elt} linbinheap_size (hp) = let
  // this algorithm is taken from a paper by Okasaki
  fun diff {nl,nr:nat | nr <= nl; nl <= nr+1} {l1:addr} .<nr>. 
    (pf_l: !bt_v (elt, nl, l1) | nr: int nr, p_l: ptr l1):<> int (nl-nr) =
    if p_l <> null then let
      prval B (pf_l_at, pf_l_l, pf_l_r) = pf_l
    in
      if nr > 0 then let
        val nr2 = nr / 2 in
        if nr > nr2 + nr2 then let
          val p_l_l = p_l->lft
          val df = diff (pf_l_l | nr2, p_l_l)
          prval () = pf_l := B (pf_l_at, pf_l_l, pf_l_r)
        in
          df
        end else let
          val p_l_r = p_l->rgh
          val df = diff (pf_l_r | nr2-1, p_l_r)
          prval () = pf_l := B (pf_l_at, pf_l_l, pf_l_r)
        in
          df
        end // end of [if]
      end else let
        prval () = pf_l := B (pf_l_at, pf_l_l, pf_l_r) in 1
      end // end of [if]
    end else let
      prval E () = pf_l; prval () = pf_l := E () in 0
    end // end of [if]
  // end of [diff]

  fun size {n:nat} {slf:addr} .<n>.
    (pf: !bt_v (elt, n, slf) | p: ptr slf):<> int n =
    if p <> null then let
      prval B (pf_at, pf_l, pf_r) = pf
      val nr = size (pf_r | p->rgh)
      val df = diff (pf_l | nr, p->lft)
      prval () = pf := B {elt} (pf_at, pf_l, pf_r)
    in
      1 + nr + nr + df
    end else let
      prval E () = pf; prval () = pf := E () in 0
    end // end of [if]
  // end of [size]
in
  size (hp.0 | hp.1)  
end // end of [linbinheap_size]

(* ****** ****** *)

implement{elt} linbinheap_insert
  {l_at} (pf_at | hp, p_at, cmp) = let
//
  prval () = lemma (pf_at) where {
    extern prfun lemma (pf_at: !btnode elt @ l_at):<prf> [l_at <> null] void
  }
//
  fun insert {n:nat}
    {l:addr} {l_at:addr | l_at <> null} .<n>. (
      pf: bt_v (elt, n, l)
    , pf_at: btnode elt @ l_at
    | p: ptr l, p_at: ptr l_at
    ) :<cloref> [l_new:addr] (bt_v (elt, n+1, l_new) | ptr l_new) =
    if p <> null then let
      prval B (pf1_at, pf_l, pf_r) = pf
      val sgn = compare_elt_elt (p->elt, p_at->elt, cmp)
    in
      if sgn >= 0 then let
        val p_l = p->lft and p_r = p->rgh
        val (pf_l_new | p_l_new) = insert (pf_r, pf1_at | p_r, p)
        val () = p_at->lft := p_l_new; val () = p_at->rgh := p_l
      in
        (B {elt} (pf_at, pf_l_new, pf_l) | p_at)
      end else let
        val p_l = p->lft and p_r = p->rgh
        val (pf_l_new | p_l_new) = insert (pf_r, pf_at | p_r, p_at)
        val () = p->lft := p_l_new; val () = p->rgh := p_l
      in
        (B {elt} (pf1_at, pf_l_new, pf_l) | p)
      end // end of [if]
    end else let
      prval E () = pf
      val () = p_at->lft := null and () = p_at->rgh := null
    in
      (B {elt} (pf_at, E (), E ()) | p_at)
    end // end of [if]
  // end of [insert]
  val (pf_rt | p_rt) = insert (hp.0, pf_at | hp.1, p_at)
in
  hp.0 := pf_rt; hp.1 := p_rt
end // end of [linbinheap_insert]

(* ****** ****** *)

fun{elt:vt0p} brauntree_ptr_leftrem {n:pos} {slf:addr} .<n>.
  (pf: !bt_v (elt, n, slf) >> bt_v (elt, n-1, slf) | rp: &ptr slf >> ptr slf)
  :<> #[slf:addr]
    [l_at:addr | l_at <> null] (btnode elt @ l_at | ptr l_at) = let
  val p = rp
  prval B (pf_at, pf_l, pf_r) = pf
  val p_l = p->lft
in
  if p_l <> null then let
    prval B (pf_l_at, pf_l_l, pf_l_r) = pf_l // prove that n1 > 0 holds
    prval pf_l = B (pf_l_at, pf_l_l, pf_l_r)
    val p_r = p->rgh
    val () = rp := p_l
    val res = brauntree_ptr_leftrem (pf_l | rp)
    val () = p->lft := p_r and () = p->rgh := rp
    val () = rp := p
    val () = pf := B {elt} (pf_at, pf_r, pf_l)
  in
    res
  end else let
    prval E () = pf_l
    val () = rp := p->rgh; prval () = pf := pf_r
  in
    (pf_at | p)
  end // end of [if]
end // end of [brauntree_ptr_leftrem]
  
(* ****** ****** *)

fun{elt:vt0p} brauntree_ptr_siftdn
  {nl,nr:nat | nr <= nl; nl <= nr+1} .<nl>.
  {l_at:addr | l_at <> null} {l1,l2:addr} (
    pf_at: btnode elt @ l_at
  , pf_l: bt_v (elt, nl, l1)
  , pf_r: bt_v (elt, nr, l2)  
  | p_at: ptr l_at, p_l: ptr l1, p_r: ptr l2
  , cmp: cmp elt
  ) :<> [l:addr] (bt_v (elt, nl+nr+1, l) | ptr l) =
  if p_l <> null then let
    prval B (pf_l_at, pf_l_l, pf_l_r) = pf_l
  in
    if p_r <> null then let
      prval B (pf_r_at, pf_r_l, pf_r_r) = pf_r
      var knd : Sgn // uninitialized
      val () = let
        val cmp_xl_x = compare_elt_elt<elt> (p_l->elt, p_at->elt, cmp)
      in
        if cmp_xl_x >= 0 then let // xl >= x
          val cmp_xr_x = compare_elt_elt<elt> (p_r->elt, p_at->elt, cmp)
        in
          if cmp_xr_x >= 0 then
            knd := 0(*N*) // xl >= x and xr >= x
          else 
            knd := 1(*R*) // x1 >= x and xr < x
          // end of [if]
        end else let // xl < x
          val cmp_xr_x = compare_elt_elt<elt> (p_r->elt, p_at->elt, cmp)
        in
          if cmp_xr_x >= 0 then
            knd := ~1(*L*) // xl < x and xr >= x
          else let
            val cmp_xl_xr = compare_elt_elt<elt> (p_l->elt, p_r->elt, cmp)
          in
            if cmp_xl_xr >= 0 then knd := 1(*R*) else knd := ~1(*L*)
          end // end of [if]
        end // end of [if]
      end // end of [val]
    in
      case+ knd of
      | _ when knd = 0 => let
          prval pf_l = B {elt} (pf_l_at, pf_l_l, pf_l_r)
          prval pf_r = B {elt} (pf_r_at, pf_r_l, pf_r_r)
          val () = p_at->lft := p_l and () = p_at->rgh := p_r
        in
          (B {elt} (pf_at, pf_l, pf_r) | p_at)
        end // end of ...
      | _ when knd < 0 => let
          prval pf_r = B {elt} (pf_r_at, pf_r_l, pf_r_r)
          val (pf_l_new | p_l_new) =
            brauntree_ptr_siftdn<elt> (pf_at, pf_l_l, pf_l_r | p_at, p_l->lft, p_l->rgh, cmp)
          // end of [val]
          val () = p_l->lft := p_l_new and () = p_l->rgh := p_r
        in
          (B {elt} (pf_l_at, pf_l_new, pf_r) | p_l)
        end // end of ...
      | _ (* knd > 0 *) => let
          prval pf_l = B {elt} (pf_l_at, pf_l_l, pf_l_r)
          val (pf_r_new | p_r_new) =
            brauntree_ptr_siftdn<elt> (pf_at, pf_r_l, pf_r_r | p_at, p_r->lft, p_r->rgh, cmp)
          // end of [val]
          val () = p_r->lft := p_l and () = p_r->rgh := p_r_new
        in
          (B {elt} (pf_r_at, pf_l, pf_r_new) | p_r)
        end // end of ...
    end else let // p_r == null
      prval E () = pf_r; prval E () = pf_l_l and E () = pf_l_r
      val sgn = compare_elt_elt<elt> (p_l->elt, p_at->elt, cmp)
    in
      if sgn >= 0 then let
        prval pf_l = B {elt} (pf_l_at, E (), E ())
        val () = p_at->lft := p_l and () = p_at->rgh := null
      in
        (B {elt} (pf_at, pf_l, E ()) | p_at)
      end else let // sgn < 0
        val () = p_at->lft := null and () = p_at->rgh := null
        val () = p_l->lft := p_at
        prval pf_l_l = B {elt} (pf_at, E (), E ()) and pf_l_r = E ()
      in
        (B {elt} (pf_l_at, pf_l_l, pf_l_r) | p_l)
      end // end of [if]
    end // end of [if]
  end else let // p_l == null
    prval E () = pf_l
    prval E () = pf_r
    val () = p_at->lft := null and () = p_at->rgh := null
  in
    (B {elt} (pf_at, E (), E ()) | p_at)
  end // end of [if]
// end of [brauntree_ptr_sifdn]

(* ****** ****** *)

implement{elt} linbinheap_delmin (hp, cmp) = let
  fn delmin {n:pos} {l:addr | l <> null} (
      pf: !bt_v (elt, n, l) >> bt_v (elt, n-1, l_new)
    | p: ptr l, cmp: cmp elt
    ) :<> #[l_new:addr] (btnode elt @ l | ptr l_new) = let
    prval B (pf_at, pf_l, pf_r) = pf
    var rp_l: ptr = p->lft
  in
    if rp_l <> null then let
      prval B (pf_l_at, pf_l_l, p_l_r) = pf_l
      prval pf_l = B {elt} (pf_l_at, pf_l_l, p_l_r)
      val (pf1_at | p1_at) = brauntree_ptr_leftrem<elt> (pf_l | rp_l)
      val (pf_new | p_new) =
        brauntree_ptr_siftdn<elt> (pf1_at, pf_r, pf_l | p1_at, p->rgh, rp_l, cmp)
      prval () = pf := pf_new
    in
      (pf_at | p_new)
    end else let // rp_l = null
      prval E () = pf_l
      prval () = pf := pf_r
      val p_new = p->rgh
    in
      (pf_at | p_new)
    end // end of [if]
  end // end of [delmin]
  stavar l : addr 
  val p = hp.1 : ptr l
in
  if p <> null then let
    prval B (pf_at, pf_l, pf_r) = hp.0
    prval pf = B {elt} (pf_at, pf_l, pf_r)
    val (pf_at | p_new) = delmin (pf | p, cmp)
    prval () = hp.0 := pf; val () = hp.1 := p_new
  in
    (Some_v {btnode elt @ l} (pf_at) | p)
  end else
    (None_v {btnode elt @ null} () | null)
  // end of [if]
end // end of [linbinheap_delmin]

(* ****** ****** *)

(* end of [linbinheap_ngc.dats] *)
