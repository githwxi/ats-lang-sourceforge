(*
**
** An implementation of functional maps based on AVL trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: August, 2009
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

(*
** An implementation of singly-linked (top-down) SPLAY trees 
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

sortdef t0p = t@ype and vt0p = viewt@ype

(* ****** ****** *)

absviewtype map_vt (key:t@ype,itm:viewt@ype+)

(* ****** ****** *)

typedef cmp (key:t@ype) = (key, key) -<cloref> Sgn

extern fun{key:t0p}
  compare_key_key (x1: key, x2: key, cmp: cmp key):<> Sgn
// end of [compare_key_key]

implement{key} compare_key_key (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

extern fun{}
linmap_empty {key:t0p;itm:vt0p} ():<> map_vt (key, itm)

extern fun{}
linmap_empty_free {key:t0p;itm:vt0p}
  (m: !map_vt (key, itm) >> opt (map_vt (key, itm), tag)): #[tag:two] int tag
// end of [linmap_empty_free]

(* ****** ****** *)

extern fun{}
linmap_is_empty {key:t0p;itm:vt0p} (m: !map_vt (key, itm)):<> bool

extern fun{}
linmap_isnot_empty {key:t0p;itm:vt0p} (m: !map_vt (key, itm)):<> bool

(* ****** ****** *)

// this is O(n)-time // but hopefully O(log n)-time
extern fun{key:t0p;itm:vt0p} linmap_height (m: !map_vt (key, itm)):<> Nat

// this is O(n)-time
extern fun{key:t0p;itm:vt0p} linmap_size (m: !map_vt (key, itm)):<> Nat

(* ****** ****** *)

viewtypedef node (
  key:t@ype, itm:viewt@ype, left:addr, right:addr
) = @{
  key= key, itm= itm, left= ptr left, right= ptr right
} // end of [node]

viewtypedef node (
  key:t@ype, itm:viewt@ype
) = @{
  key= key, itm= itm
, left= ptr?, right= ptr?
} // end of [node]

typedef
node0 (key:t@ype,itm:viewt@ype) = node (key, itm)?
// end of [node0]

dataview
tree_v (
  key : t@ype
, itm : viewt@ype+
, int  // size
, addr // self
) = (* view for singly linked binary trees *)
  | {nl,nr:nat} {lft,rgh:addr} {slf:addr | slf <> null}
    B (key, itm, nl+nr+1, slf) of (
      node (key, itm, lft, rgh) @ slf
    , tree_v (key, itm, nl, lft), tree_v (key, itm, nr, rgh)
    ) // end of [B]
  | E (key, itm, 0, null) of ()
// end of [dataview tree_v]

(* ****** ****** *)

fun{key:t0p;itm:vt0p}
  tree_height_get {n:nat} {slf:addr} .<n>.
  (pf: !tree_v (key, itm, n, slf) | p: ptr slf):<> Nat =
  if p <> null then let
    prval B (pf_at, pf_l, pf_r) = pf
    val hl = tree_height_get (pf_l | p->left)
    val hr = tree_height_get (pf_r | p->right)
    prval () = pf := B (pf_at, pf_l, pf_r)
  in
     if hl >= hr then 1+hl else 1+hr
  end else
    0 // the height of empty tree
  // end of [if]
// end of [tree_height_get]

(* ****** ****** *)

dataview
ldiff_v (
  key : t@ype
, itm : viewt@ype+
, int  // size
, addr // the root of missing left child
, addr // root
, addr // self
) = (* view for a binary tree where a subtree is missing *)
  | {n1,n2:nat} {lft,rgh,pnt:addr} {rt:addr} {slf:addr | slf <> null}
    LB1 (key, itm, n1+n2+1, lft, rt, slf) of (
      node (key, itm, lft, rgh) @ slf
    , ldiff_v (key, itm, n1, slf, rt, pnt), tree_v (key, itm, n2, rgh)
    ) // end of [B]
  | {chld:addr} LE1 (key, itm, 0, chld, chld, null) of ()
// end of [dataview ldiff_v]

(* ****** ****** *)

fn{key:t0p;itm:vt0p} ldiff_child_set
  {n:nat} {chld0,chld1:addr} {rt:addr} {slf:addr} (
    fpf: !ldiff_v (key, itm, n, chld0, rt, slf) >> ldiff_v (key, itm, n, chld1, rt, slf)
  | pt: ptr rt, p: ptr slf, pc1: ptr chld1
  ) :<> #[rt:addr] ptr rt =
  if p <> null then let
    prval LB1 (pf_at, fpf_l, pf_r) = fpf
    val () = p->left := pc1
    prval () = fpf := LB1 (pf_at, fpf_l, pf_r)
  in
    pt
  end else let
    prval LE1 () = fpf; prval () = fpf := LE1 () in pc1
  end // end of [if]
// end of [ldiff_child_set]

(* ****** ****** *)

fun{key:t0p;itm:vt0p} ldiff_tree_join
  {n1,n2:nat}
  {chld0,chld1:addr} {rt:addr} 
  {slf:addr} .<n1>. (
    fpf: ldiff_v (key, itm, n1, chld0, rt, slf), pf0: tree_v (key, itm, n2, chld1)
  | pt: ptr rt, p: ptr slf, pc1: ptr chld1
  ) :<> [slf:addr] (
    tree_v (key, itm, n1+n2, slf) | ptr slf
  ) = let
//
prfun lemma_ldiff_tree_join
  {n1,n2:nat} {chld:addr} {rt:addr} {slf:addr} .<n1>. (
    fpf: ldiff_v (key, itm, n1, chld, rt, slf), pf0: tree_v (key, itm, n2, chld)
  ) :<> tree_v (key, itm, n1+n2, rt) =
  case+ fpf of
  | LB1 (pf_at, fpf_l, pf_r) => lemma_ldiff_tree_join (fpf_l, B (pf_at, pf0, pf_r))
  | LE1 () => pf0
//
in
  if p <> null then let
    prval LB1 (pf_at, fpf_l, pf_r) = fpf
    val () = p->left := pc1
    prval pf = lemma_ldiff_tree_join (LB1 (pf_at, fpf_l, pf_r), pf0)
  in
    (pf | pt)
  end else let
    prval LE1 () = fpf in (pf0 | pc1)
  end // end of [if]
end (* ldiff_tree_join *)

(* ****** ****** *)

dataview
rdiff_v (
  key : t@ype
, itm : viewt@ype+
, int  // size
, addr // the root of missing left child
, addr // root
, addr // self
) = (* view for a binary tree where a subtree is missing *)
  | {n1,n2:nat} {lft,rgh,pnt:addr} {rt:addr} {slf:addr | slf <> null}
    RB1 (key, itm, n1+n2+1, rgh, rt, slf) of (
      node (key, itm, lft, rgh) @ slf
    , tree_v (key, itm, n2, lft), rdiff_v (key, itm, n1, slf, rt, pnt)
    ) // end of [B]
  | {chld:addr} RE1 (key, itm, 0, chld, chld, null) of ()
// end of [dataview ldiff_v]

(* ****** ****** *)

fn{key:t0p;itm:vt0p} rdiff_child_set
  {n:nat} {chld0,chld1:addr} {rt:addr} {slf:addr} (
    fpf: !rdiff_v (key, itm, n, chld0, rt, slf) >> rdiff_v (key, itm, n, chld1, rt, slf)
  | pt: ptr rt, p: ptr slf, pc1: ptr chld1
  ) :<> #[rt:addr] ptr rt =
  if p <> null then let
    prval RB1 (pf_at, pf_l, fpf_r) = fpf
    val () = p->right := pc1
    prval () = fpf := RB1 (pf_at, pf_l, fpf_r)
  in
    pt
  end else let
    prval RE1 () = fpf; prval () = fpf := RE1 () in pc1
  end // end of [if]
// end of [rdiff_child_set]

(* ****** ****** *)

fun{key:t0p;itm:vt0p} rdiff_tree_join
  {n1,n2:nat}
  {chld0,chld1:addr} {rt:addr} 
  {slf:addr} .<n1>. (
    fpf: rdiff_v (key, itm, n1, chld0, rt, slf), pf0: tree_v (key, itm, n2, chld1)
  | pt: ptr rt, p: ptr slf, pc1: ptr chld1
  ) :<> [slf:addr] (
    tree_v (key, itm, n1+n2, slf) | ptr slf
  ) = let
//
prfun lemma_rdiff_tree_join {key:t0p;itm:vt0p}
  {n1,n2:nat} {chld:addr} {rt:addr} {slf:addr} .<n1>. (
    fpf: rdiff_v (key, itm, n1, chld, rt, slf), pf0: tree_v (key, itm, n2, chld)
  ) :<> tree_v (key, itm, n1+n2, rt) =
  case+ fpf of
  | RB1 (pf_at, pf_l, fpf_r) => lemma_rdiff_tree_join (fpf_r, B (pf_at, pf_l, pf0))
  | RE1 () => pf0
//
in
  if p <> null then let
    prval RB1 (pf_at, pf_l, fpf_r) = fpf
    val () = p->right := pc1
    prval pf = lemma_rdiff_tree_join (RB1 (pf_at, pf_l, fpf_r), pf0)
  in
    (pf | pt)
  end else let
    prval RE1 () = fpf in (pf0 | pc1)
  end // end of [if]
end // end of [rdiff_tree_join]

(* ****** ****** *)

fun{key:t0p;itm:vt0p} tree_splay_loop
  {ln:nat;lchld,lrt,lslf:addr}
  {rn:nat;rchld,rrt,rslf:addr}
  {n:nat} {slf:addr | slf <> null} .<n>. (
    lfpf: rdiff_v (key, itm, ln, lchld, lrt, lslf)
  , rfpf: ldiff_v (key, itm, rn, rchld, rrt, rslf)
  , pf: !tree_v (key, itm, n, slf) >> tree_v (key, itm, ln+n+rn, slf)
  | lpt: ptr lrt, lp: ptr lslf
  , rpt: ptr rrt, rp: ptr rslf
  , p: ptr slf, k0: key, cmp: cmp key
  ) :<> #[slf:addr | slf <> null] ptr slf = let
  prval B (pf_at, pf_l, pf_r) = pf
  val sgn = compare_key_key (k0, p->key, cmp)
in
  if sgn < 0 then let
    val p_l = p->left
  in
    if p_l <> null then let
      prval B (pf_l_at, pf_l_l, pf_l_r) = pf_l
      val () = p->left := p_l->right
      val sgn1 = compare_key_key (k0, p_l->key, cmp)
    in
      if sgn1 < 0 then let // zig-zig-rotation
        val p_l_l = p_l->left
      in
        if p_l_l <> null then let
          prval () = pf := pf_l_l
          val () = p_l->right := p
          val rpt = ldiff_child_set (rfpf | rpt, rp, p_l)
          prval rfpf = LB1 (pf_l_at, rfpf, B (pf_at, pf_l_r, pf_r))
        in
          tree_splay_loop (lfpf, rfpf, pf | lpt, lp, rpt, p_l, p_l_l, k0, cmp)
        end else let
          prval E () = pf_l_l
          prval pf_r = B (pf_at, pf_l_r, pf_r)
          val (pf_l | lpt) = rdiff_tree_join (lfpf, E () | lpt, lp, null)
          val (pf_r | rpt) = ldiff_tree_join (rfpf, pf_r | rpt, rp, p)
          val () = p_l->left := lpt
          val () = p_l->right := rpt
          prval () = pf := B (pf_l_at, pf_l, pf_r)
        in
          p_l // the key [k0] is not found
        end (* end of [if] *)
      end else let // sgn1 >= 0: zig-rotation
        val rpt = ldiff_child_set (rfpf | rpt, rp, p)
        prval rfpf = LB1 (pf_at, rfpf, pf_r)
        prval () = pf := B (pf_l_at, pf_l_l, pf_l_r)
      in
        tree_splay_loop (lfpf, rfpf, pf | lpt, lp, rpt, p, p_l, k0, cmp)
      end // end of [if]
    end else let
      val (pf_l | lpt) = rdiff_tree_join (lfpf, pf_l | lpt, lp, p->left)
      val (pf_r | rpt) = ldiff_tree_join (rfpf, pf_r | rpt, rp, p->right)
      val () = p->left := lpt
      val () = p->right := rpt
      prval () = pf := B (pf_at, pf_l, pf_r)
    in
      p // the key [k0] is not found
    end (* end of [if] *)
  end else if sgn > 0 then let
    val p_r = p->right
  in
    if p_r <> null then let
      prval B (pf_r_at, pf_r_l, pf_r_r) = pf_r
      val () = p->right := p_r->left
      val sgn1 = compare_key_key (k0, p_r->key, cmp)
    in
      if sgn1 > 0 then let // zag-zag-rotation
        val p_r_r = p_r->right
      in
        if p_r_r <> null then let
          prval () = pf := pf_r_r
          val () = p_r->left := p
          val lpt = rdiff_child_set (lfpf | lpt, lp, p_r)
          prval lfpf = RB1 (pf_r_at, B (pf_at, pf_l, pf_r_l), lfpf)
        in
          tree_splay_loop (lfpf, rfpf, pf | lpt, p_r, rpt, rp, p_r_r, k0, cmp)
        end else let
          prval E () = pf_r_r
          prval pf_l = B (pf_at, pf_l, pf_r_l)
          val (pf_l | lpt) = rdiff_tree_join (lfpf, pf_l | lpt, lp, p)
          val (pf_r | rpt) = ldiff_tree_join (rfpf, E () | rpt, rp, null)
          val () = p_r->left := lpt
          val () = p_r->right := rpt
          prval () = pf := B (pf_r_at, pf_l, pf_r)
        in
          p_r // the key [k0] is not found
        end (* end of [if] *)
      end else let // sgn1 <= 0: zag-rotation
        val lpt = rdiff_child_set (lfpf | lpt, lp, p)
        prval lfpf = RB1 (pf_at, pf_l, lfpf)
        prval () = pf := B (pf_r_at, pf_r_l, pf_r_r)
      in
        tree_splay_loop (lfpf, rfpf, pf | lpt, p, rpt, rp, p_r, k0, cmp)
      end // end of [if]
    end else let
      val (pf_l | lpt) = rdiff_tree_join (lfpf, pf_l | lpt, lp, p->left)
      val (pf_r | rpt) = ldiff_tree_join (rfpf, pf_r | rpt, rp, p->right)
      val () = p->left := lpt
      val () = p->right := rpt
      prval () = pf := B (pf_at, pf_l, pf_r)
    in
      p // the key [k0] is not found
    end // end of [if]
  end else let // sgn = 0
    val (pf_l | lpt) = rdiff_tree_join (lfpf, pf_l | lpt, lp, p->left)
    val (pf_r | rpt) = ldiff_tree_join (rfpf, pf_r | rpt, rp, p->right)
    val () = p->left := lpt
    val () = p->right := rpt
    prval () = pf := B (pf_at, pf_l, pf_r)
  in
    p // the key [k0] is found
  end // end of [if]
end (* end of [tree_splay_loop] *)

fn{key:t0p;itm:vt0p} tree_splay
  {n:nat} {slf:addr | slf <> null} (
    pf: !tree_v (key, itm, n, slf) >> tree_v (key, itm, n, slf)
  | p: ptr slf, k0: key, cmp: cmp key
  ) :<> #[slf:addr | slf <> null] ptr slf = let
in
  tree_splay_loop (
    RE1 (), LE1 (), pf | null(*lpt*), null(*lp*), null(*rpt*), null(*rp*), p, k0, cmp
  ) // end of [tree_splay_loop]
end // end of [tree_splay]

(* ****** ****** *)

assume map_vt (key:t0p, itm:vt0p) =
  [n:nat;slf:addr] (tree_v (key, itm, n, slf) | ptr slf)
// end of [map_vt]

(* ****** ****** *)

implement{} linmap_empty {key,itm} () = (E {key,itm} () | null)

implement{}
  linmap_empty_free {key,itm} (m) = let
  viewtypedef map_vt = map_vt (key, itm) in
  if m.1 <> null then let
    prval () = opt_some {map_vt} (m) in 1
  end else let
    prval E () = m.0; prval () = opt_none {map_vt} (m) in 0
  end (* end of [if] *)
end (* end of [linmap_empty_free] *)

(* ****** ****** *)

implement{} linmap_is_empty (m) = (m.1 = null)
implement{} linmap_isnot_empty (m) = (m.1 <> null)

(* ****** ****** *)

implement{key,itm} // not tail-recursive
  linmap_height (m) = tree_height_get (m.0 | m.1)
// end of [linmap_height]

(* ****** ****** *)

implement{key,itm} // not tail-recursive
  linmap_size (t) = aux (t.0 | t.1) where {
  fun aux {n:nat} {slf:addr} .<n>.
    (pf: !tree_v (key, itm, n, slf) | p: ptr slf):<> int n =
    if p <> null then let
      prval B (pf_at, pf_l, pf_r) = pf
      val res = aux (pf_l | p->left) + 1 + aux (pf_r | p->right)
      prval () = pf := B (pf_at, pf_l, pf_r)
    in
      res
    end else let
      prval E () = pf; prval () = pf := E () in 0
    end // end of [if]
  // end of [aux]
} // end of [linmap_size]

(* ****** ****** *)

extern fun{key,itm:t0p}
  linmap_search {l_res:addr} (
    pf_res: !itm? @ l_res >> disj_v (itm? @ l_res, itm @ l_res, tag)
  | m: &map_vt (key, itm)
  , k0: key
  , p_res: ptr l_res
  , cmp: cmp key
  ) :<> #[tag:two] int tag
// end of [linmap_search]

implement{key,itm} linmap_search
  {l_res} (pf_res | m, k0, p_res, cmp) = let
  viewdef V0 = itm? @ l_res and V1 = itm @ l_res
  val pt = m.1
in
  if pt <> null then let
    val pt = tree_splay<key,itm> (m.0 | pt, k0, cmp)
    val () = m.1 := pt
    prval B (pf_at, pf_l, pf_r) = m.0
    val k1 = pt->key
    val sgn = compare_key_key (k0, k1, cmp)
  in
    if sgn = 0 then let
      val () = !p_res := pt->itm
      prval () = pf_res := InsRight_v {V0,V1} (pf_res)
      prval () = m.0 := B (pf_at, pf_l, pf_r)
    in
      1 // item associated with the given key [k0] is found
    end else let
      prval () = pf_res := InsLeft_v {V0,V1} (pf_res)
      prval () = m.0 := B (pf_at, pf_l, pf_r)
    in
      0 // item associated with the given key [k0] is found
    end // end of [if]
  end else let
    prval () = pf_res := InsLeft_v {V0,V1} (pf_res)
  in
    0 // item associated with the given key [k0] is not found
  end // end of [if]
end (* end of [linmap_search] *)

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p}
linmap_insert {l_at:addr} (
    pf_at: !node (key, itm) @ l_at >> option_v (node (key, itm) @ l_at, tag > 0)
  | m: &map_vt (key, itm), p_at: ptr l_at, cmp: cmp key
  ) :<> #[tag:two] int tag
// end of [linmap_insert]

implement{key,itm}
  linmap_insert {l_at} (pf_at | m, p_at, cmp) = let
//
  prval () = lemma (pf_at) where {
    extern prfun lemma (pf: !node (key, itm) @ l_at):<prf> [l_at <> null] void
  } // end of [prval]
//
  viewdef V = node (key, itm) @ l_at
  val pt = m.1
in
  if pt <> null then let
    val k0 = p_at->key
    val pt = tree_splay<key,itm> (m.0 | pt, k0, cmp)
    prval B (pf1_at, pf1_l, pf1_r) = m.0
    val sgn = compare_key_key (k0, pt->key, cmp)
  in
    if sgn < 0 then let
      val () = p_at->left := pt->left
      val () = p_at->right := pt
      val () = pt->left := null
      prval () = m.0 := B {key,itm} (pf_at, pf1_l, B (pf1_at, E (), pf1_r))
      val () = m.1 := p_at
      prval () = pf_at := None_v {V} ()
    in
      0 // insertion is performed
    end else if sgn > 0 then let
      val () = p_at->left := pt
      val () = p_at->right := pt->right
      val () = pt->right := null
      prval () = m.0 := B {key,itm} (pf_at, B (pf1_at, pf1_l, E ()), pf1_r)
      val () = m.1 := p_at
      prval () = pf_at := None_v {V} ()
    in
      0 // insertion is performed
    end else let
      val () = m.0 := B {key,itm} (pf1_at, pf1_l, pf1_r)
      val () = m.1 := pt
      prval () = pf_at := Some_v {V} (pf_at)
    in
      1 // insertion is not performed
    end // end of [if]
  end else let
    prval E () = m.0
    val () = m.1 := p_at
    val () = p_at->left := null
    val () = p_at->right := null
    prval () = m.0 := B {key,itm} (pf_at, E (), E ())
    prval () = pf_at := None_v {V} ()
  in
    0 // insertion is performed
  end // end of [if]
end (* end of [linmap_insert] *)

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p}
linmap_remove {l_at:addr} (
    m: &map_vt (key, itm), k0: key, cmp: cmp key
  ) :<> [l_at:addr] (
    option_v (node (key, itm) @ l_at, l_at <> null) | ptr l_at
  )
// end of [linmap_remove]

implement{key,itm}
  linmap_remove {l_at} (m, k0, cmp) = let
    viewdef V0 = node (key,itm) @ null
  val pt = m.1
in
  if pt <> null then let
    val pt = tree_splay<key,itm> (m.0 | pt, k0, cmp)
    stavar rt: addr
    viewdef V1 = node (key,itm) @ rt
    val _(*dummy*) = pt : ptr rt // for typeckecking only
    prval B (pf_at, pf_l, pf_r) = m.0
    val sgn = compare_key_key (k0, pt->key, cmp)
  in
    if sgn = 0 then let // the key [k0] is found
      val pt_l = pt->left
    in
      if pt_l <> null then let
        val pt_l = tree_splay<key,itm> (pf_l | pt_l, k0, cmp)
        prval B (pf_l_at, pf_l_l, pf_l_r) = pf_l
//
        val () = $effmask_exn (assert (pt_l->right = null)) // lhs <= k0 < rhs !!!
//
        prval E () = pf_l_r
        val () = pt_l->right := pt->right
        prval () = m.0 := B {key,itm} (pf_l_at, pf_l_l, pf_r)
        val () = m.1 := pt_l
      in
        (Some_v {V1} (pf_at) | pt)
      end else let
        prval E () = pf_l
        prval () = m.0 := pf_r
        val () = m.1 := pt->right
      in
        (Some_v {V1} (pf_at) | pt)
      end // end of [if]
    end else let // the key [k0] is not found
      prval () = m.0 := B (pf_at, pf_l, pf_r)
      val () = m.1 := pt
    in
      (None_v {V0} () | null)
    end // end of [if]
  end else
    (None_v {V0} () | null) // the key [k0] is not found
  // end of [if]
end (* end of [linmap_remove] *)

(* ****** ****** *)

// infix order foreach
fun{key:t0p;itm:vt0p} tree_foreach_inf
  {v:view} {vt:viewtype} {n:nat} {slf:addr} {f:eff} .<n>. (
    pf1: !tree_v (key,itm,n,slf)
  , pf2: !v
  | p: ptr slf
  , f: (!v | key, &itm, !vt) -<f> void
  , env: !vt
  ) :<f> void = let
in
  if p <> null then let
    prval B (pf1_at, pf1_l, pf1_r) = pf1
    val () = tree_foreach_inf (pf1_l, pf2 | p->left, f, env)
    val () = f (pf2 | p->key, p->itm, env)
    val () = tree_foreach_inf (pf1_r, pf2 | p->right, f, env)
    prval () = pf1 := B (pf1_at, pf1_l, pf1_r)
  in
    // nothing
  end // end of [if]
end // end of [bst_foreach_inf]

(* ****** ****** *)

extern fun{key:t0p;itm:vt0p} linmap_foreach_clo {v:view}
  (pf: !v | xs: !map_vt (key, itm), f: &(!v | key, &itm) -<clo> void):<> void

implement{key,itm}
  linmap_foreach_clo {v} (pf1 | m, f) = let
  viewtypedef clo_t = (!v | key, &itm) -<clo> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | k: key, i: &itm, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | k, i)
    prval () = pf := (pf1, pf2)
  in
    // empty
  end // end of [app]
  prval pf2 = view@ f; prval pf = (pf1, pf2)
  val () = tree_foreach_inf<key,itm> {V} {ptr l_f} (m.0, pf | m.1, app, p_f)
  prval () = (pf1 := pf.0; view@ f := pf.1)
in
  // empty
end // end of [linmap_foreach_clo]

(* ****** ****** *)

(*

// for the purpose of debugging

extern
fun{key:t0p;itm:vt0p}
print_tree {n:nat} {slf:addr}
  (pf: !tree_v (key,itm,n,slf) | p: ptr slf): void
  = "print_tree"

extern
fun{key:t0p;itm:vt0p}
print_tree_dummy {slf:addr} (p: ptr slf): void
  = "print_tree"

extern fun{key:t0p;itm:vt0p} print_linmap (map: !map_vt (key,itm)): void

implement{key,itm} print_linmap (map) = print_tree (map.0 | map.1)

*)

(* ****** ****** *)

(* end of [linmap_splaytree_ngc.dats] *)
