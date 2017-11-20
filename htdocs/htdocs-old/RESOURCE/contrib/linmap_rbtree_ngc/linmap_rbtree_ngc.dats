(*
**
** An implementation of functional maps based on red-black trees.
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
** An implementation of doubly-linked red-black trees
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

// this is O(n)-time
extern fun{key:t0p;itm:vt0p} linmap_size (m: !map_vt (key, itm)):<> Nat

// this is O(log n)-time
extern fun{key:t0p;itm:vt0p} linmap_black_height (m: !map_vt (key, itm)):<> Nat

(* ****** ****** *)

#define RED 1; #define BLK 0

(* ****** ****** *)

viewtypedef rbnode (
  key:t@ype, itm:viewt@ype, color:int, left:addr, right:addr, parent:addr
) = @{
  key= key, itm= itm
, color= int color
, left= ptr left, right= ptr right
, parent= ptr parent
} // end of [rbnode]

viewtypedef rbnode (
  key:t@ype, itm:viewt@ype
) = @{
  key= key, itm= itm
, color= int?
, left= ptr?, right= ptr?
, parent= ptr?
} // end of [rbnode]

typedef
rbnode0 (key:t@ype,itm:viewt@ype) = rbnode (key, itm)?
// end of [rbnode0]

sortdef clr = {c: int | 0 <= c; c <= 1}

dataprop clr_p
  (int(*c*), int(*c1*), int(*c2*), int(*v*)) =
  | {c1,c2:clr} CLRred (RED, c1, c2, c1+c2) | {c1,c2:clr} CLRblk (BLK, c1, c2, 0)
// end of [color_p]

dataview
rbtree_v (
  key : t@ype
, itm : viewt@ype+
, int  // color (red=1/black=0)
, int  // black height
, int  // color violation
, addr // parent
, addr // self
) = (* view for doubly-linked red-black trees *)
  | {c,c1,c2:clr} {bh:nat} {v:int}
    {lft,rgh,pnt:addr} {slf:addr | slf <> null}
    B (key, itm, c, bh+1-c, v, pnt, slf) of (
      clr_p (c, c1, c2, v)
    , rbnode (key, itm, c, lft, rgh, pnt) @ slf
    , rbtree_v (key, itm, c1, bh, 0, slf, lft)
    , rbtree_v (key, itm, c2, bh, 0, slf, rgh)
    ) // end of [R] // black node
  | {pnt:addr} E (key, itm, BLK, 0, 0, pnt, null) of ()
// end of [dataview rbtree_v]

(* ****** ****** *)

prfn clr_lemma {c,c1,c2:clr} {v:int}
  (pf: clr_p (c, c1, c2, v))
  :<prf> [c == 0 || c1+c2 == v] void =
  case+ pf of CLRred () => () | CLRblk () => ()
// end of [clr_lemma]

prfn vio_lemma {key:t0p;itm:vt0p}
  {c:clr} {bh:int} {v:int | v > 0} {pnt:addr} {slf:addr}
  (pf: !rbtree_v (key, itm, c, bh, v, pnt, slf)):<> [c==RED] void = let
  prval B (pf_clr, pf_at, pf_l, pf_r) = pf
  prval CLRred () = pf_clr
  prval () = pf := B (pf_clr, pf_at, pf_l, pf_r)
in
  // nothing
end // end of [vio_lemma]

(* ****** ****** *)

fn{key:t0p;itm:vt0p} rbtree_color_get
  {c:int} {bh:nat} {v:int} {pnt:addr} {slf:addr}
  (pf: !rbtree_v (key, itm, c, bh, v, pnt, slf) | p: ptr slf):<> int c =
  if p <> null then let
    prval B (pf_clr, pf_at, pf_l, pf_r) = pf
    val c = p->color
    prval () = pf := B (pf_clr, pf_at, pf_l, pf_r)
  in
    c
  end else let
    prval E () = pf; prval () = pf := E {key,itm} {pnt} ()
  in
    BLK
  end // end of [if]
// end of [rbtree_color_get]

fn{key:t0p;itm:vt0p}
  rbtree_color_trans_red_blk
  {c:int} {bh:nat} {v:int} {pnt:addr} {slf:addr} (
    pf: !rbtree_v (key, itm, RED, bh, 0, pnt, slf)
           >> rbtree_v (key, itm, BLK, bh+1, 0, pnt, slf)
  | p: ptr slf
  ) :<> void = let
  prval B (pf_clr, pf_at, pf_l, pf_r) = pf
  val () = p->color := BLK
  prval pf_clr = CLRblk ()
  prval () = pf := B (pf_clr, pf_at, pf_l, pf_r)
in
  // nothing
end // end of [rbtree_color_trans_red_blk]

(* ****** ****** *)

fn{key:t0p;itm:vt0p} rbtree_parent_set
  {c:clr} {bh:nat} {v:int}
  {pnt0:addr} {slf:addr} {pnt1:addr} (
    pf: !rbtree_v (key, itm, c, bh, v, pnt0, slf)
           >> rbtree_v (key, itm, c, bh, v, pnt1, slf)
  | p: ptr slf, pp1: ptr pnt1
  ) :<> void =
  if p <> null then let
    prval B (pf_clr, pf_at, pf_l, pf_r) = pf
    val () = p->parent := pp1
    prval () = pf := B (pf_clr, pf_at, pf_l, pf_r)
  in
    // nothin
  end else let
    prval E () = pf; prval () = pf := E {key,itm} {pnt1} ()
  in
    // nothing
  end // end of [if]
// end of [rbtree_parent_set]

(* ****** ****** *)

(*
** left rotation for restoring color invariant
*)
fn{key:t0p;itm:vt0p} rbtree_lrotate
  {c1:clr}
  {bh:nat}
  {lft,rgh,pnt:addr}
  {slf:addr | slf <> null} (
    pf_at: rbnode (key, itm, BLK, lft, rgh, pnt) @ slf
  , pf_l : rbtree_v (key, itm, c1, bh, 0, slf, lft), pf_r : rbtree_v (key, itm, RED, bh, 1, slf, rgh)
  | p: ptr slf
  ) :<> [slf:addr] (
    rbtree_v (key, itm, 1(*red*), bh+1, 0, pnt, slf) | ptr slf
  ) = let
  val p_r = p->right
  prval B (pf_r_clr, pf_r_at, pf_r_l, pf_r_r) = pf_r
  prval () = clr_lemma (pf_r_clr)
  val p_r_l = p_r->left and p_r_r = p_r->right
  val c_r_r = rbtree_color_get (pf_r_r | p_r_r)
in
  if c_r_r = RED then let // shallow rotation
(*
** T (B, a, x, T (R, b, y, T (R, c, z, d))) => T (R, T (B, a, x, b), y, T (B, c, z, d))
*)
    val () = p_r->parent := p->parent
    val () = p_r->left := p
    val () = p->parent := p_r
//
    val () = p->right := p_r_l
    val () = rbtree_parent_set<key,itm> (pf_r_l | p_r_l, p)
//
    val () = rbtree_color_trans_red_blk<key,itm> (pf_r_r | p_r_r)
//
    prval pf_l = B {key,itm} (CLRblk, pf_at, pf_l, pf_r_l)
    prval pf_r = pf_r_r
  in
    (B (CLRred (), pf_r_at, pf_l, pf_r) | p_r)
  end else let // c_l_r = RED and c_r_r = BLK: deep rotation
(*
** T (B, a, x, T (R, T (R, b, y, c), z, d)) => T (R, T (B, a, x, b), y, T (B, c, z, d))
*)
    prval B (pf_r_l_clr, pf_r_l_at, pf_r_l_l, pf_r_l_r) = pf_r_l
    prval () = clr_lemma (pf_r_l_clr)
//
    val p_r_l_l = p_r_l->left
    val p_r_l_r = p_r_l->right
//
    val () = p_r_l->parent := p->parent
    val () = p_r_l->left := p
    val () = p->parent := p_r_l
    val () = p_r_l->right := p_r
    val () = p_r->parent := p_r_l
//
    val () = p->right := p_r_l_l
    val () = rbtree_parent_set<key,itm> (pf_r_l_l | p_r_l_l, p)
    prval pf_l = B {key,itm} (CLRblk (), pf_at, pf_l, pf_r_l_l)
//
    val () = p_r->color := BLK
    val () = p_r->left := p_r_l_r
    val () = rbtree_parent_set<key,itm> (pf_r_l_r | p_r_l_r, p_r)
    prval pf_r = B {key,itm} (CLRblk (), pf_r_at, pf_r_l_r, pf_r_r)
//
  in
    (B (CLRred (), pf_r_l_at, pf_l, pf_r) | p_r_l)
  end // end of [if]
end (* end of [rbtree_lrotate] *)

(* ****** ****** *)

(*
** right rotation for restoring color invariant
*)
fn{key:t0p;itm:vt0p} rbtree_rrotate
  {c2:clr}
  {bh:nat}
  {lft,rgh,pnt:addr}
  {slf:addr | slf <> null} (
    pf_at: rbnode (key, itm, BLK, lft, rgh, pnt) @ slf
  , pf_l : rbtree_v (key, itm, RED, bh, 1, slf, lft), pf_r : rbtree_v (key, itm, c2, bh, 0, slf, rgh)
  | p: ptr slf
  ) :<> [slf:addr] (
    rbtree_v (key, itm, 1(*red*), bh+1, 0, pnt, slf) | ptr slf
  ) = let
  val p_l = p->left
  prval B (pf_l_clr, pf_l_at, pf_l_l, pf_l_r) = pf_l
  prval () = clr_lemma (pf_l_clr)
  val p_l_l = p_l->left and p_l_r = p_l->right
  val c_l_l = rbtree_color_get<key,itm> (pf_l_l | p_l_l)
in
  if c_l_l = RED then let // shallow rotation
(*
** T(B, T (R, T (R, a, x, b), y, c), z, d) => T (R, T (B, a, x, b), y, T (B, c, z, d))
*)
    val () = p_l->parent := p->parent
    val () = p_l->right := p
    val () = p->parent := p_l
//
    val () = rbtree_color_trans_red_blk<key,itm> (pf_l_l | p_l_l)
//
    val () = p->left := p_l_r
    val () = rbtree_parent_set<key,itm> (pf_l_r | p_l_r, p)
//
    prval pf_l = pf_l_l
    prval pf_r = B {key,itm} (CLRblk, pf_at, pf_l_r, pf_r)
  in
    (B (CLRred (), pf_l_at, pf_l, pf_r) | p_l)
  end else let // c_l_l = BLK and c_l_r = RED: deep rotation
(*
** T (B, T (R, a, x, T (R, b, y, c)), z, d) => T (R, T (B, a, x, b), y, T (B, c, z, d))
*)
    prval B (pf_l_r_clr, pf_l_r_at, pf_l_r_l, pf_l_r_r) = pf_l_r
    prval () = clr_lemma (pf_l_r_clr)
//
    val p_l_r_l = p_l_r->left
    val p_l_r_r = p_l_r->right
//
    val () = p_l_r->parent := p->parent
    val () = p_l_r->left := p_l
    val () = p_l->parent := p_l_r
    val () = p_l_r->right := p
    val () = p->parent := p_l_r
//
    val () = p_l->color := BLK
    val () = p_l->right := p_l_r_l
    val () = rbtree_parent_set<key,itm> (pf_l_r_l | p_l_r_l, p_l)
    prval pf_l = B (CLRblk (), pf_l_at, pf_l_l, pf_l_r_l)
//
    val () = p->left := p_l_r_r
    val () = rbtree_parent_set<key,itm> (pf_l_r_r | p_l_r_r, p)
    prval pf_r = B {key,itm} (CLRblk (), pf_at, pf_l_r_r, pf_r)
//
  in
    (B (CLRred (), pf_l_r_at, pf_l, pf_r) | p_l_r)
  end // end of [if]
end (* end of [rbtree_rrotate] *)

(* ****** ****** *)

assume map_vt (key:t0p, itm:vt0p) =
  [c:clr;bh:nat;slf:addr] (rbtree_v (key, itm, c, bh, 0, null, slf) | ptr slf)
// end of [map_vt]

(* ****** ****** *)

implement{} linmap_empty {key,itm} () = (E {key,itm} {null} () | null)

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

implement{key,itm}
  linmap_size (m) = aux (m.0 | m.1) where {
  fun aux {c:clr} {bh:nat} // non-tail-recursive
    {v:nat} {pnt:addr} {slf:addr} .<2*bh+c+v>. (
      pf: !rbtree_v (key, itm, c, bh, v, pnt, slf) | p: ptr slf
    ) :<> Nat =
    if p <> null then let
      prval B {..} {c,c1,c2} {bh1} (pf_clr, pf_at, pf_l, pf_r) = pf
      prval () = clr_lemma (pf_clr)
      val res = aux (pf_l | p->left) + 1 + aux (pf_r | p->right)
      prval () = pf := B (pf_clr, pf_at, pf_l, pf_r)
    in
      res
    end else let
      prval E () = pf; prval () = pf := E () in 0
    end // end of [if]
  // end of [aux]
} // end of [linmap_size]

(* ****** ****** *)

implement{key,itm}
  linmap_black_height (m) = loop (m.0 | m.1, 0) where {
  fun loop {c:clr} {bh:nat} // [loop] is tail-recursive
    {v:nat} {pnt:addr} {slf:addr} {n:nat} .<2*bh+c+v>. (
      pf: !rbtree_v (key, itm, c, bh, v, pnt, slf) | p: ptr slf, n: int n
    ) :<> int (n + bh) =
    if p <> null then let
      prval B (pf_clr, pf_at, pf_l, pf_r) = pf
      val c = p->color
      prval () = clr_lemma (pf_clr)
      val res = loop (pf_l | p->left, n+1-c)
      prval () = pf := B (pf_clr, pf_at, pf_l, pf_r)
    in
      res
    end else let
      prval E () = pf; prval () = pf := E () in n
    end // end of [if]
  // end of [loop]
} // end of [linmap_black_height]

(* ****** ****** *)

extern fun{key,itm:t0p}
  linmap_search {l_res:addr} (
    pf_res: !itm? @ l_res >> disj_v (itm? @ l_res, itm @ l_res, tag)
  | m: !map_vt (key, itm)
  , k0: key
  , p_res: ptr l_res
  , cmp: cmp key
  ) :<> #[tag:two] int tag
// end of [linmap_search]

implement{key,itm} linmap_search {l_res}
  (pf_res | m, k0, p_res, cmp) = search (m.0, pf_res | m.1) where {
  var res: itm // uninitialized
  viewdef V0 = itm? @ l_res and V1 = itm @ l_res
  fun search {c:clr} {bh:nat}
    {v:nat} {pnt:addr} {slf:addr} .<2*bh+c+v>. (
      pf: !rbtree_v (key, itm, c, bh, v, pnt, slf), pf_res: !V0 >> disj_v (V0, V1, tag)
    | p: ptr slf
    ) :<cloref> #[tag:two] int tag =
    if p <> null then let
      prval B (pf_clr, pf_at, pf_l, pf_r) = pf
      prval () = clr_lemma (pf_clr)
      val sgn = compare_key_key (k0, p->key, cmp)
    in
      case+ sgn of
      | ~1 => let
          val tag = search (pf_l, pf_res | p->left)
          prval () = pf := B (pf_clr, pf_at, pf_l, pf_r)
        in
          tag
        end // end of [~1]
      |  1 => let
          val tag = search (pf_r, pf_res | p->right)
          prval () = pf := B (pf_clr, pf_at, pf_l, pf_r)
        in
          tag
        end // end of [ 1]
      | _ (*0*) => let
          val () = !p_res := p->itm
          prval () = pf := B (pf_clr, pf_at, pf_l, pf_r)
          prval () = pf_res := InsRight_v {V0,V1} (pf_res)
        in
          1 // item associated with the given key [k0] is found
        end // end of [0]
    end else let
      prval () = pf_res := InsLeft_v {V0,V1} (pf_res) in 0
    end // end of [if]
} // end of [linmap_search]

(* ****** ****** *)

dataview rbdiff_v (
  key : t@ype
, itm : viewt@ype+
, int  // root color
, int  // the color of the missing rbtree
, int  // root black height
, int  // the black height of the missing rbtree
, addr // child: the root of the missing rbtree
, int  // direction: left(0) or right(1)
, addr // root
, addr // root parent
, addr // self
) = (* view for an rbtree minus a sub rbtree *)
  | {c,c1,c11,c12:clr} {bh,bh11:nat | bh11+1 <= bh+c1}
    {lft,rgh,pnt:addr} {dir:two} {rt,rtp:addr}
    {slf:addr | slf <> null}
    B1L (key, itm, c, c11, bh, bh11, lft, 0(*dir*), rt, rtp, slf) of (
      clr_p (c1, c11, c12, 0)
    , rbnode (key, itm, c1, lft, rgh, pnt) @ slf
    , rbdiff_v (key, itm, c, c1, bh, bh11+1-c1, slf, dir, rt, rtp, pnt)
    , rbtree_v (key, itm, c12, bh11, 0, slf, rgh)
    ) // end of [B1L]
  | {c,c1,c11,c12:clr} {bh,bh11:nat | bh11+1 <= bh+c1}
    {lft,rgh,pnt:addr} {dir:two} {rt,rtp:addr}
    {slf:addr | slf <> null}
    B1R (key, itm, c, c12, bh, bh11, rgh, 1(*dir*), rt, rtp, slf) of (
      clr_p (c1, c11, c12, 0)
    , rbnode (key, itm, c1, lft, rgh, pnt) @ slf
    , rbtree_v (key, itm, c11, bh11, 0, slf, lft)
    , rbdiff_v (key, itm, c, c1, bh, bh11+1-c1, slf, dir, rt, rtp, pnt)
    ) // end of [B1R]
  | {c:clr} {bh:nat} {chld:addr} {dir:two} {slf:addr}
    E1 (key, itm, c, c, bh, bh, chld, dir, chld, slf, slf) of ()
// end of [rbdiff_v]

(* ****** ****** *)

prfun rbdiff_rbtree_join {key:t0p;itm:vt0p}
  {c,c1:clr} {bh,bh1:nat | bh1 <= bh} {chld:addr} {dir:two} {rt,rtp:addr}
  {slf:addr} .<2*(bh-bh1)+1-c1>. (
    fpf: rbdiff_v (key, itm, c, c1, bh, bh1, chld, dir, rt, rtp, slf)
  , pf0: rbtree_v (key, itm, c1, bh1, 0, slf, chld) // view for the missing rbtree
  ) :<prf> rbtree_v (key, itm, c, bh, 0, rtp, rt) =
  case+ fpf of
  | B1L (pf_clr, pf_at, fpf_l, pf_r) => let
      prval () = clr_lemma (pf_clr)
    in
      rbdiff_rbtree_join (fpf_l, B (pf_clr, pf_at, pf0, pf_r))
    end // end of [B1L]
  | B1R (pf_clr, pf_at, pf_l, fpf_r) => let
      prval () = clr_lemma (pf_clr)
    in
      rbdiff_rbtree_join (fpf_r, B (pf_clr, pf_at, pf_l, pf0))
    end // end of [B1R]
  | E1 () => pf0
// end of [rbdiff_rbtree_join]

(* ****** ****** *)

prfun rbdiff_takeout {key:t0p;itm:vt0p}
  {c,c1x:clr} {bh,bh11:int} {chld:addr} {dir:int} {rt,rtp:addr}
  {slf:addr | slf <> rtp} .<>. (
    fpf: rbdiff_v (key, itm, c, c1x, bh, bh11, chld, dir, rt, rtp, slf)
  ) :<prf> [c1:int;lft,rgh,pnt:addr] (
    rbnode (key, itm, c1, lft, rgh, pnt) @ slf
  , rbnode (key, itm, c1, lft, rgh, pnt) @ slf
      -<lin> rbdiff_v (key, itm, c, c1x, bh, bh11, chld, dir, rt, rtp, slf)
  ) = case+ fpf of
  | B1L {..} {_1,c1,_2,_3} {..} {lft,rgh,pnt} (pf_clr, pf_at, fpf_l, pf_r) =>
      #[c1,lft,rgh,pnt | (pf_at, llam (pf_at) => B1L (pf_clr, pf_at, fpf_l, pf_r))]
    // end of [B1L]
  | B1R {..} {_1,c1,_2,_3} {..} {lft,rgh,pnt} (pf_clr, pf_at, pf_l, fpf_r) =>
      #[c1,lft,rgh,pnt | (pf_at, llam (pf_at) => B1R (pf_clr, pf_at, pf_l, fpf_r))]
    // end of [B1R]
(* end of [rbdiff_takeout] *)

(* ****** ****** *)

fn{key:t0p;itm:vt0p} rbdiff_dir_get
  {c,c1:clr} {bh,bh1:int}
  {chld:addr | chld <> null} {dir:int} {rt:addr}
  {slf:addr} (
    fpf: !rbdiff_v (key, itm, c, c1, bh, bh1, chld, dir, rt, null, slf) | p: ptr slf, pc: ptr chld
  ) :<> int dir = let
  val dir = if p <> null then let
    prval (pf_at, ffpf) = rbdiff_takeout (fpf)
    val dir = (if pc = p->left then 0(*left*) else 1(*right*)): int
    prval () = fpf := ffpf (pf_at)
  in
    dir
  end else begin
    0 // it is arbitrarily chosen (from {0,1})
  end : int
in
  __cast (dir) where { extern castfn __cast (_: int):<> int dir }
end // end of [rbdiff_dir_get]

(* ****** ****** *)

fn{key:t0p;itm:vt0p} rbdiff_child_set
  {c,c1:clr} {bh,bh1:int}
  {chld:addr} {dir:int} {rt,rtp:addr}
  {slf:addr | slf <> rtp}
  {chld1:addr} (
    fpf: !rbdiff_v (key, itm, c, c1, bh, bh1, chld, dir, rt, rtp, slf)
           >> rbdiff_v (key, itm, c, c1, bh, bh1, chld1, dir, rt, rtp, slf)
    // end of [fpf]
  | p: ptr slf, dir: int dir, pc1: ptr chld1
  ) :<> void =
  if dir = 0 then let
    prval B1L (pf_clr, pf_at, fpf1, pf2) = fpf
    val () = p->left := pc1
    prval () = fpf := B1L (pf_clr, pf_at, fpf1, pf2)
  in
    // nothing
  end else let
    prval B1R (pf_clr, pf_at, pf1, fpf2) = fpf
    val () = p->right := pc1
    prval () = fpf := B1R (pf_clr, pf_at, pf1, fpf2)
  in
    // nothing
  end // end of [if]
// end of [rbdiff_child_set]

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p}
  rbtree_split {c:clr} {bh:nat} {rt:addr} (
    pf: rbtree_v (key, itm, c, bh, 0, null, rt)
  | p: &ptr rt >> ptr slf, k0: key, dir: &int 0 >> int dir, cmp: cmp key
  ) :<> #[dir:two;slf:addr]
    [c0:clr;bh0:nat;chld:addr | bh0 <= bh] (
    rbdiff_v (key, itm, c, c0, bh, bh0, chld, dir, rt, null, slf)
  , rbtree_v (key, itm, c0, bh0, 0, slf, chld)
  | ptr chld
  )
// end of [rbtree_split]

implement{key,itm} rbtree_split
  {c} {bh} {rt} (pf | p, k0, dir, cmp) = let
  fun loop {c0:clr} {bh0:nat | bh0 <= bh}
    {chld:addr} {dir:two} {slf:addr} .<2*bh0+c0>. (
      fpf: rbdiff_v (key, itm, c, c0, bh, bh0, chld, dir, rt, null, slf),
      pf: rbtree_v (key, itm, c0, bh0, 0, slf, chld)
    | p: &ptr slf >> ptr slf, pc: ptr chld, dir: &int dir >> int dir
  ) :<cloref> #[dir:two;slf:addr]
    [c1:clr] [bh1:nat | bh1 <= bh0] [chld:addr] (
    rbdiff_v (key, itm, c, c1, bh, bh1, chld, dir, rt, null, slf)
  , rbtree_v (key, itm, c1, bh1, 0, slf, chld)
  | ptr chld
  ) =
  if pc <> null then let
    prval B (pf_clr, pf_at, pf_l, pf_r) = pf
    prval () = clr_lemma (pf_clr)
    val sgn = compare_key_key (k0, pc->key, cmp)
  in
    if sgn < 0 then let
      val () = p := pc
      val () = dir := 0(*left*)
      val pc_l = pc->left
    in
      loop (B1L {key,itm} (pf_clr, pf_at, fpf, pf_r), pf_l | p, pc_l, dir)
    end else if sgn > 0 then let
      val () = p := pc
      val () = dir := 1(*right*)
      val pc_r = pc->right
    in
      loop (B1R {key,itm} (pf_clr, pf_at, pf_l, fpf), pf_r | p, pc_r, dir)
    end else // sgn = 0
      (fpf, B (pf_clr, pf_at, pf_l, pf_r) | pc)
    // end of [if]
  end else
    (fpf, pf | pc)
  (* end of [if] *)
  val pc = p
  val () = p := null
  prval fpf = E1 ()
in
  loop (fpf, pf | p, pc, dir)
end // end of [rbtree_split]

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p} balanceIns
  {c,c0,c1:clr}
  {bh,bh0:nat} {v0:nat | v0 <= c0}
  {chld0,chld1:addr} {dir:two} {rt:addr}
  {slf:addr} (
    fpf: rbdiff_v (key, itm, c, c0, bh, bh0, chld0, dir, rt, null, slf)
  , pf0: rbtree_v (key, itm, c1, bh0, v0, slf, chld1) // view for the missing rbtree
  | c0: int c0, v0: int v0, pc0: ptr chld0, dir: int dir, pt: ptr rt, p: ptr slf
  , pc1: ptr chld1
  ) :<> [c:clr;bh':nat;slf:addr | bh <= bh'; bh' <= bh+1]
    (rbtree_v (key, itm, c, bh', 0(*violation*), null, slf) | ptr slf)
// end of [balanceIns]

implement{key,itm} balanceIns
  (fpf, pf0 | c0, v0, pc0, dir, pt, p, pc1) = let
in
  if p <> null then let
    val c1 = rbtree_color_get<key,itm> (pf0 | pc1)
  in
    if dir = 0(*left*) then let
      prval B1L (pf_clr, pf_at, fpf1, pf2) = fpf
      prval () = clr_lemma (pf_clr)
      val pp = p->parent
      val c0p = p->color
      val dirp = rbdiff_dir_get<key,itm> (fpf1 | pp, p)
      val () = p->left := pc1
    in
      if c0 = RED then begin
        if v0 > 0 then let
          prval () = vio_lemma (pf0) // c1 == RED
          val (pf_new | p_new) = rbtree_rrotate<key,itm> (pf_at, pf0, pf2 | p)
        in
          balanceIns (fpf1, pf_new | c0p, 0(*violation*), p, dirp, pt, pp, p_new)
        end else begin
          if c1 = RED then let
            prval fpf = B1L {key,itm} (pf_clr, pf_at, fpf1, pf2)
          in
            (rbdiff_rbtree_join {key,itm} (fpf, pf0) | pt)
          end else let
            val () = p->color := BLK
            prval pf_new = B {key,itm} (CLRblk, pf_at, pf0, pf2)
          in
            balanceIns (fpf1, pf_new | c0p, 0(*violation*), p, dirp, pt, pp, p)
          end // end of [if]
        end // end of [if]
      end else begin // c0 = BLK
        if c0p = RED then let
          prval pf_new = B {key,itm} (CLRred, pf_at, pf0, pf2)
        in
          balanceIns (fpf1, pf_new | c0p, c1(*violation*), p, dirp, pt, pp, p)
        end else let
          prval pf_new = B (CLRblk, pf_at, pf0, pf2)
        in
          balanceIns (fpf1, pf_new | c0p,  0(*violation*), p, dirp, pt, pp, p)
        end // end of [if]
      end // end of [if]
    end else let // dir = 1(*right*)
      prval B1R (pf_clr, pf_at, pf1, fpf2) = fpf
      prval () = clr_lemma (pf_clr)
      val pp = p->parent
      val c0p = p->color
      val dirp = rbdiff_dir_get<key,itm> (fpf2 | pp, p)
      val () = p->right := pc1
    in
      if c0 = RED then begin
        if v0 > 0 then let
          prval () = vio_lemma (pf0) // c1 == RED
          val (pf_new | p_new) = rbtree_lrotate<key,itm> (pf_at, pf1, pf0 | p)
        in
          balanceIns (fpf2, pf_new | c0p, 0(*violation*), p, dirp, pt, pp, p_new)
        end else begin
          if c1 = RED then let
            prval fpf = B1R (pf_clr, pf_at, pf1, fpf2)
          in
            (rbdiff_rbtree_join {key,itm} (fpf, pf0) | pt)
          end else let
            val () = p->color := BLK
            prval pf_new = B {key,itm} (CLRblk, pf_at, pf1, pf0)
          in
            balanceIns (fpf2, pf_new | c0p, 0(*violation*), p, dirp, pt, pp, p)
          end // end of [if]
        end // end of [if]
      end else begin // c0 = BLK
        if c0p = RED then let
          prval pf_new = B (CLRred, pf_at, pf1, pf0)
        in
          balanceIns (fpf2, pf_new | c0p, c1(*violation*), p, dirp, pt, pp, p)
        end else let
          prval pf_new = B (CLRblk, pf_at, pf1, pf0)
        in
          balanceIns (fpf2, pf_new | c0p,  0(*violation*), p, dirp, pt, pp, p)
        end // end of [if]
      end // end of [if]
    end // end of [if]
  end else let
    prval E1 () = fpf
  in
    if v0 > 0 then let
      prval B (pf0_clr, pf0_at, pf0_l, pf0_r) = pf0
      prval () = clr_lemma pf0_clr
      val () = pc1->color := BLK
      prval () = pf0 := B (CLRblk, pf0_at, pf0_l, pf0_r)
    in
      (pf0 | pc1)      
    end else begin
      (pf0 | pc1)
    end // end of [if]
  end // end of [if]
end // end of [balanceIns]

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p}
linmap_insert {l_at:addr} (
    pf_at: !rbnode (key, itm) @ l_at
             >> option_v (rbnode (key, itm) @ l_at, tag > 0)
  | m: &map_vt (key, itm), p_at: ptr l_at, cmp: cmp key
  ) :<> #[tag:two] int tag
// end of [linmap_insert]

implement{key,itm}
  linmap_insert {l_at} (pf_at | m, p_at, cmp) = let
//
  prval () = lemma (pf_at) where {
    extern prfun lemma (pf: !rbnode (key, itm) @ l_at):<prf> [l_at <> null] void
  } // end of [prval]
//
  val pt = m.1
  var p = pt
  val k0 = p_at->key
  var dir: int = 0
  val (fpf, pf0 | pc0) = rbtree_split (m.0 | p, k0, dir, cmp)
in
  if pc0 <> null then let
    prval pf = rbdiff_rbtree_join {key,itm} (fpf, pf0)
    prval () = pf_at := Some_v (pf_at)
  in
    m.0 := pf; 1 (*tag*) // no insertion is performed
  end else let
    prval E () = pf0
    val () = p_at->color := RED
    val () = p_at->parent := p
    val () = p_at->left := null
    val () = p_at->right := null
    prval pf0 = B {key,itm} (CLRred, pf_at, E (), E ())
    prval () = pf_at := None_v ()
    val (pf | p_new) = balanceIns<key,itm> (fpf, pf0 | BLK, 0, pc0, dir, pt, p, p_at)
  in
    m.0 := pf; m.1 := p_new; 0 (*tag*) // insertion is performed
  end // end of [if]
end (* end of [linmap_insert] *)

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p} balanceRem0
  {c,c0,c1:clr | c1 <= c0}
  {bh,bh0:nat}
  {chld0,chld1:addr} {dir:two} {rt:addr}
  {slf:addr} (
    fpf: rbdiff_v (key, itm, c, c0, bh, bh0, chld0, dir, rt, null, slf)
  , pf0: rbtree_v (key, itm, c1, bh0, 0, slf, chld1) // view for the missing rbtree
  | c0: int c0, pc0: ptr chld0, dir: int dir, pt: ptr rt, p: ptr slf
  , pc1: ptr chld1
  ) :<> [c':clr;slf:addr | c' <= c]
    (rbtree_v (key, itm, c', bh, 0(*violation*), null, slf) | ptr slf)
// end of [balanceRem0]

implement{key,itm} balanceRem0
  {c,c0,c1} {bh,bh0} {chld0,chld1} {dir} {rt} {slf}
  (fpf, pf0 | c0, pc0, dir, pt, p, pc1) =
  if p <> null then let
(*
** // nothing    
*)
  in
    if dir = 0(*left*) then let
      prval B1L {..} {c,c0p,c_l,c_r} (pf_clr, pf_at, fpf1, pf2) = fpf
      prval () = clr_lemma (pf_clr)
      val () = p->left := pc1
      prval pf_clr_new = (
        case+ pf_clr of CLRred () => CLRred | CLRblk () => CLRblk
      ) : clr_p (c0p, c1, c_r, 0)
      prval pf = rbdiff_rbtree_join {key,itm} (fpf1, B (pf_clr_new, pf_at, pf0, pf2))
    in
      (pf | pt)
    end else let // dir = 1(*right*)
      prval B1R {..} {c,c0p,c_l,c_r} (pf_clr, pf_at, pf1, fpf2) = fpf
      prval () = clr_lemma (pf_clr)
      val () = p->right := pc1
      prval pf_clr_new = (
        case+ pf_clr of CLRred () => CLRred | CLRblk () => CLRblk
      ) : clr_p (c0p, c_l, c1, 0)
      prval pf = rbdiff_rbtree_join {key,itm} (fpf2, B (pf_clr_new, pf_at, pf1, pf0))
    in
      (pf | pt)
    end // end of [if]
  end else let
    prval E1 () = fpf in (pf0 | pc1)
  end // end of [if]
// end of [balanceRem0]

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p} balanceRem1
  {c,c0:clr}
  {bh,bh1:nat}
  {chld0,chld1:addr} {dir:two} {rt:addr}
  {slf:addr} (
    fpf: rbdiff_v (key, itm, c, c0, bh, bh1+1, chld0, dir, rt, null, slf)
  , pf0: rbtree_v (key, itm, BLK, bh1, 0, slf, chld1) // view for the missing rbtree
  | c0: int c0, pc0: ptr chld0, dir: int dir, pt: ptr rt, p: ptr slf
  , pc1: ptr chld1, bhdf: &int? >> int (bh-bh')
  ) :<> #[c':clr;bh':nat | c' <= c; bh' <= bh; bh <= bh'+1-c']
    [slf:addr] (rbtree_v (key, itm, c', bh', 0(*violation*), null, slf) | ptr slf)
// end of [balanceRem1]

extern
fun{key:t0p;itm:vt0p} balanceRem1_left
  {c,c0:clr} {bh,bh1:nat}
  {chld0,chld1:addr} {rt:addr}
  {slf:addr | slf <> null} (
    fpf: rbdiff_v (key, itm, c, c0, bh, bh1+1, chld0, 0(*left*), rt, null, slf)
  , pf0: rbtree_v (key, itm, BLK, bh1, 0, slf, chld1) // view for the missing rbtree
  | c0: int c0, pc0: ptr chld0, pt: ptr rt, p: ptr slf
  , pc1: ptr chld1, bhdf: &int? >> int (bh-bh')
  ) :<> #[c':clr;bh':nat | c' <= c; bh' <= bh; bh <= bh'+1-c']
    [slf:addr] (rbtree_v (key, itm, c', bh', 0(*violation*), null, slf) | ptr slf)
// end of [balanceRem1_left]

extern
fun{key:t0p;itm:vt0p} balanceRem1_right
  {c,c0:clr} {bh,bh1:nat}
  {chld0,chld1:addr} {rt:addr}
  {slf:addr | slf <> null} (
    fpf: rbdiff_v (key, itm, c, c0, bh, bh1+1, chld0, 1(*right*), rt, null, slf)
  , pf0: rbtree_v (key, itm, BLK, bh1, 0, slf, chld1) // view for the missing rbtree
  | c0: int c0, pc0: ptr chld0, pt: ptr rt, p: ptr slf
  , pc1: ptr chld1, bhdf: &int? >> int (bh-bh')
  ) :<> #[c':clr;bh':nat | c' <= c; bh' <= bh; bh <= bh'+1-c']
    [slf:addr] (rbtree_v (key, itm, c', bh', 0(*violation*), null, slf) | ptr slf)
// end of [balanceRem1_right]

(* ****** ****** *)

implement{key,itm}
  balanceRem1 (fpf, pf0 | c0, pc0, dir, pt, p, pc1, bhdf) =
  if p <> null then (
    if dir = 0 then 
      balanceRem1_left<key,itm> (fpf, pf0 | c0, pc0, pt, p, pc1, bhdf)
    else
      balanceRem1_right<key,itm> (fpf, pf0 | c0, pc0, pt, p, pc1, bhdf)
    // end of [if]
  ) else (
    let prval E1 () = fpf; val () = bhdf := 1 in (pf0 | pc1) end
  ) // end of [if]
(* end of [balanceRem1] *)

(* ****** ****** *)

implement{key,itm} balanceRem1_left
  (fpf, pf0 | c0, pc0, pt, p, pc1, bhdf) = let
  prval B1L (pf_clr, pf_at, fpf_l, pf_r) = fpf
  prval () = clr_lemma (pf_clr)
//
  val pp = p->parent
  stavar c0p: int
  val c0p = p->color : int c0p
  val dirp = rbdiff_dir_get<key,itm> (fpf_l | pp, p)
//
  val p_r = p->right
  prval B (pf_r_clr, pf_r_at, pf_r_l, pf_r_r) = pf_r
  prval () = clr_lemma (pf_r_clr)
  val c_r = p_r->color
  val p_r_l = p_r->left
in
  if c_r = BLK then let
    val c_r_l = rbtree_color_get (pf_r_l | p_r_l)
  in
    if c_r_l = RED then let
      prval B (pf_r_l_clr, pf_r_l_at, pf_r_l_l, pf_r_l_r) = pf_r_l
      prval () = clr_lemma (pf_r_l_clr)
//
      val p_r_l_l = p_r_l->left
      val p_r_l_r = p_r_l->right
//
      val () = p_r_l->color := c0p
      val () = p_r_l->parent := pp
      val () = p_r_l->left := p
      val () = p->parent := p_r_l
      val () = p_r_l->right := p_r
      val () = p_r->parent := p_r_l
//
      val () = p->color := BLK
      val () = p->left := pc1
      val () = p->right := p_r_l_l
      val () = rbtree_parent_set<key,itm> (pf_r_l_l | p_r_l_l, p)
      prval pf_l = B {key,itm} (CLRblk, pf_at, pf0, pf_r_l_l)
//
      val () = p_r->left := p_r_l_r
      val () = rbtree_parent_set<key,itm> (pf_r_l_r | p_r_l_r, p_r)
      prval pf_r = B {key,itm} (CLRblk, pf_r_at, pf_r_l_r, pf_r_r)
//
      prval pf0_clr = (
        case+ pf_clr of CLRred () => CLRred () | CLRblk () => CLRblk
      ) : clr_p (c0p, BLK, BLK, 0)
      prval pf0_new = B {key,itm} (pf0_clr, pf_r_l_at, pf_l, pf_r)
//
      val () = bhdf := 0
//
    in
      balanceRem0 (fpf_l, pf0_new | c0p, p, dirp, pt, pp, p_r_l)
    end else let // c_r_l = BLK
      val () = p_r->parent := pp
      val () = p_r->left := p
      val () = p->parent := p_r
//
      val () = p->color := RED
      val () = p->left := pc1
      val () = p->right := p_r_l
      val () = rbtree_parent_set<key,itm> (pf_r_l | p_r_l, p)
//
      prval pf_l = B {key,itm} (CLRred, pf_at, pf0, pf_r_l)
      prval pf0_new = B {key,itm} (CLRblk, pf_r_at, pf_l, pf_r_r)
    in
      if c0p = RED then let
        val () = bhdf := 0
      in
        balanceRem0 (fpf_l, pf0_new | c0p, p, dirp, pt, pp, p_r)
      end else
        balanceRem1 (fpf_l, pf0_new | c0p, p, dirp, pt, pp, p_r, bhdf)
      // end of [if]
    end // end of [if]
  end else let // c_r = RED
    prval B (pf_r_l_clr, pf_r_l_at, pf_r_l_l, pf_r_l_r) = pf_r_l
    prval () = clr_lemma (pf_r_l_clr)
    val p_r_l_l = p_r_l->left
    val p_r_l_r = p_r_l->right
    val c_r_l_r = rbtree_color_get (pf_r_l_r | p_r_l_r)
  in
    if c_r_l_r = RED then let
      val () = p_r_l->parent := pp
      val () = p_r_l->left := p
      val () = p->parent := p_r_l
      val () = p_r_l->right := p_r
      val () = p_r->parent := p_r_l
      val () = p->left := pc1
      val () = p->right := p_r_l_l
      val () = rbtree_parent_set<key,itm> (pf_r_l_l | p_r_l_l, p)
      prval pf_l = B {key,itm} (CLRblk, pf_at, pf0, pf_r_l_l)
      val () = p_r->left := p_r_l_r
      val () = rbtree_parent_set<key,itm> (pf_r_l_r | p_r_l_r, p_r)
      val () = rbtree_color_trans_red_blk (pf_r_l_r | p_r_l_r)
      prval pf_r = B {key,itm} (CLRred, pf_r_at, pf_r_l_r, pf_r_r)
      prval pf0_new = B {key,itm} (CLRblk, pf_r_l_at, pf_l, pf_r)
//
      val () = bhdf := 0
//
    in
      balanceRem0 (fpf_l, pf0_new | c0p, p, dirp, pt, pp, p_r_l)
    end else let // c_r_l_r = BLK
      val c_r_l_l = rbtree_color_get<key,itm> (pf_r_l_l | p_r_l_l)
    in
      if c_r_l_l = BLK then let
        val () = p_r->parent := pp
        val () = p_r->color := BLK
        val () = p_r->left := p
        val () = p->parent := p_r
        val () = p->left := pc1
        val () = p->right := p_r_l
        val () = p_r_l->parent := p
        val () = p_r_l->color := RED
        prval pf_r_l = B {key,itm} (CLRred, pf_r_l_at, pf_r_l_l, pf_r_l_r)
        prval pf_l = B {key,itm} (CLRblk, pf_at, pf0, pf_r_l)
        prval pf0_new = B {key,itm} (CLRblk, pf_r_at, pf_l, pf_r_r)
//
        val () = bhdf := 0
//
      in
        balanceRem0 (fpf_l, pf0_new | c0p, p, dirp, pt, pp, p_r)
      end else let // c_r_l_l = RED
        prval B (pf_r_l_l_clr, pf_r_l_l_at, pf_r_l_l_l, pf_r_l_l_r) = pf_r_l_l
        prval () = clr_lemma (pf_r_l_l_clr)
        val p_r_l_l_l = p_r_l_l->left and p_r_l_l_r = p_r_l_l->right
        val () = p_r->parent := pp
        val () = p_r->color := BLK
        val () = p_r->left := p_r_l_l
        val () = p_r_l_l->parent := p_r
//
        val () = p_r_l_l->color := BLK
        val () = p_r_l_l->left := p
        val () = p->parent := p_r_l_l
        val () = p_r_l_l->right := p_r_l
        val () = p_r_l->parent := p_r_l_l
//
        val () = p->color := RED
        val () = p->left := pc1
        val () = p->right := p_r_l_l_l
        val () = rbtree_parent_set<key,itm> (pf_r_l_l_l | p_r_l_l_l, p)
//
        val () = p_r_l->color := RED
        val () = p_r_l->left := p_r_l_l_r
        val () = rbtree_parent_set<key,itm> (pf_r_l_l_r | p_r_l_l_r, p_r_l)
//
        prval pf_l_l = B {key,itm} (CLRred, pf_at, pf0, pf_r_l_l_l)
        prval pf_l_r = B {key,itm} (CLRred, pf_r_l_at, pf_r_l_l_r, pf_r_l_r)
        prval pf_l = B {key,itm} (CLRblk, pf_r_l_l_at, pf_l_l, pf_l_r)
        prval pf0_new = B {key,itm} (CLRblk, pf_r_at, pf_l, pf_r_r)
//
        val () = bhdf := 0
//
      in
        balanceRem0 (fpf_l, pf0_new | c0p, p, dirp, pt, pp, p_r)
      end // end of [if c_r_l_l = BLK]
    end // end of [if c_r_l_r = RED]
  end // end of [if c_r = BLK]
end (* end of [balanceRem1_left] *)

(* ****** ****** *)

implement{key,itm} balanceRem1_right
  (fpf, pf0 | c0, pc0, pt, p, pc1, bhdf) = let
  prval B1R (pf_clr, pf_at, pf_l, fpf_r) = fpf
  prval () = clr_lemma (pf_clr)
//
  val pp = p->parent
  stavar c0p: int
  val c0p = p->color : int c0p
  val dirp = rbdiff_dir_get<key,itm> (fpf_r | pp, p)
//
  val p_l = p->left
  prval B (pf_l_clr, pf_l_at, pf_l_l, pf_l_r) = pf_l
  prval () = clr_lemma (pf_l_clr)
  val c_l = p_l->color
  val p_l_r = p_l->right
in
  if c_l = BLK then let
    val c_l_r = rbtree_color_get (pf_l_r | p_l_r)
  in
    if c_l_r = RED then let
      prval B (pf_l_r_clr, pf_l_r_at, pf_l_r_l, pf_l_r_r) = pf_l_r
      prval () = clr_lemma (pf_l_r_clr)
//
      val p_l_r_l = p_l_r->left
      val p_l_r_r = p_l_r->right
//
      val () = p_l_r->color := c0p
      val () = p_l_r->parent := pp
      val () = p_l_r->left := p_l
      val () = p_l->parent := p_l_r
      val () = p_l_r->right := p
      val () = p->parent := p_l_r
//
      val () = p_l->right := p_l_r_l
      val () = rbtree_parent_set<key,itm> (pf_l_r_l | p_l_r_l, p_l)
      prval pf_l = B {key,itm} (CLRblk, pf_l_at, pf_l_l, pf_l_r_l)
//
      val () = p->color := BLK
      val () = p->left := p_l_r_r
      val () = rbtree_parent_set<key,itm> (pf_l_r_r | p_l_r_r, p)
      val () = p->right := pc1
      prval pf_r = B {key,itm} (CLRblk, pf_at, pf_l_r_r, pf0)
//
      prval pf0_clr = (
        case+ pf_clr of CLRred () => CLRred () | CLRblk () => CLRblk
      ) : clr_p (c0p, BLK, BLK, 0)
      prval pf0_new = B {key,itm} (pf0_clr, pf_l_r_at, pf_l, pf_r)
//
      val () = bhdf := 0
//
    in
      balanceRem0 (fpf_r, pf0_new | c0p, p, dirp, pt, pp, p_l_r)
    end else let // c_l_r = BLK
      val () = p_l->parent := pp
      val () = p_l->right := p
      val () = p->parent := p_l
//
      val () = p->color := RED
      val () = p->left := p_l_r
      val () = rbtree_parent_set<key,itm> (pf_l_r | p_l_r, p)
      val () = p->right := pc1
//
      prval pf_r = B {key,itm} (CLRred, pf_at, pf_l_r, pf0)
      prval pf0_new = B {key,itm} (CLRblk, pf_l_at, pf_l_l, pf_r)
    in
      if c0p = RED then let
        val () = bhdf := 0
      in
        balanceRem0 (fpf_r, pf0_new | c0p, p, dirp, pt, pp, p_l)
      end else
        balanceRem1 (fpf_r, pf0_new | c0p, p, dirp, pt, pp, p_l, bhdf)
      // end of [if]
    end // end of [if]
  end else let // c_l = RED
    prval B (pf_l_r_clr, pf_l_r_at, pf_l_r_l, pf_l_r_r) = pf_l_r
    prval () = clr_lemma (pf_l_r_clr)
    val p_l_r_l = p_l_r->left
    val p_l_r_r = p_l_r->right
    val c_l_r_l = rbtree_color_get (pf_l_r_l | p_l_r_l)
  in
    if c_l_r_l = RED then let
      val () = p_l_r->parent := pp
      val () = p_l_r->left := p_l
      val () = p_l->parent := p_l_r
      val () = p_l_r->right := p
      val () = p->parent := p_l_r
      val () = p->left := p_l_r_r
      val () = p->right := pc1
      val () = rbtree_parent_set<key,itm> (pf_l_r_r | p_l_r_r, p)
      val () = p_l->right := p_l_r_l
      val () = rbtree_parent_set<key,itm> (pf_l_r_l | p_l_r_l, p_l)
      val () = rbtree_color_trans_red_blk (pf_l_r_l | p_l_r_l)
      prval pf_l = B {key,itm} (CLRred, pf_l_at, pf_l_l, pf_l_r_l)
      prval pf_r = B {key,itm} (CLRblk, pf_at, pf_l_r_r, pf0)
      prval pf0_new = B {key,itm} (CLRblk, pf_l_r_at, pf_l, pf_r)
//
      val () = bhdf := 0
//
    in
      balanceRem0 (fpf_r, pf0_new | c0p, p, dirp, pt, pp, p_l_r)
    end else let // c_l_r_l = BLK
      val c_l_r_r = rbtree_color_get<key,itm> (pf_l_r_r | p_l_r_r)
    in
      if c_l_r_r = BLK then let
        val () = p_l->parent := pp
        val () = p_l->color := BLK
        val () = p_l->right := p
        val () = p->parent := p_l
        val () = p->left := p_l_r
        val () = p_l_r->parent := p
        val () = p->right := pc1
        val () = p_l_r->color := RED
        prval pf_l_r = B {key,itm} (CLRred, pf_l_r_at, pf_l_r_l, pf_l_r_r)
        prval pf_r = B {key,itm} (CLRblk, pf_at, pf_l_r, pf0)
        prval pf0_new = B {key,itm} (CLRblk, pf_l_at, pf_l_l, pf_r)
//
        val () = bhdf := 0
//
      in
        balanceRem0 (fpf_r, pf0_new | c0p, p, dirp, pt, pp, p_l)
      end else let // c_l_r_r = RED
        prval B (pf_l_r_r_clr, pf_l_r_r_at, pf_l_r_r_l, pf_l_r_r_r) = pf_l_r_r
        prval () = clr_lemma (pf_l_r_r_clr)
        val p_l_r_r_l = p_l_r_r->left and p_l_r_r_r = p_l_r_r->right
//
        val () = p_l->parent := pp
        val () = p_l->color := BLK
        val () = p_l->right := p_l_r_r
        val () = p_l_r_r->parent := p_l
//
        val () = p_l_r_r->color := BLK
        val () = p_l_r_r->left := p_l_r
        val () = p_l_r->parent := p_l_r_r
        val () = p_l_r_r->right := p
        val () = p->parent := p_l_r_r
//
        val () = p_l_r->color := RED
        val () = p_l_r->right := p_l_r_r_l
        val () = rbtree_parent_set<key,itm> (pf_l_r_r_l | p_l_r_r_l, p_l_r)
//
        val () = p->color := RED
        val () = p->left := p_l_r_r_r
        val () = rbtree_parent_set<key,itm> (pf_l_r_r_r | p_l_r_r_r, p)
        val () = p->right := pc1
//
        prval pf_r_l = B {key,itm} (CLRred, pf_l_r_at, pf_l_r_l, pf_l_r_r_l)
        prval pf_r_r = B {key,itm} (CLRred, pf_at, pf_l_r_r_r, pf0)
        prval pf_r = B {key,itm} (CLRblk, pf_l_r_r_at, pf_r_l, pf_r_r)
        prval pf0_new = B {key,itm} (CLRblk, pf_l_at, pf_l_l, pf_r)
//
        val () = bhdf := 0
//
      in
        balanceRem0 (fpf_r, pf0_new | c0p, p, dirp, pt, pp, p_l)
      end // end of [if c_l_r_r = BLK]
    end // end of [if c_l_r_l = RED]
  end // end of [if c_r = BLK]
end (* end of [balanceRem1_right] *)

(* ****** ****** *)

(*

extern
fun{key:t0p;itm:vt0p}
rbtree_remove_min
  {c:clr} {bh:nat} {rt:addr | rt <> null} (
    pf: rbtree_v (key, itm, c, bh, 0, null, rt)
  | pt: &ptr rt >> ptr rt, bhdf: &int? >> int (bh-bh')
  ) :<> #[ 
    c':clr;bh':nat;rt:addr | c' <= c; bh' <= bh; bh <= bh'+1-c'
  ] [slf:addr | slf <> null] (
    rbnode (key, itm) @ slf, rbtree_v (key, itm, c', bh', 0, null, rt) | ptr slf
  )
// end of [rbtree_remove_min]

implement{key,itm}
  rbtree_remove_min {c} {bh} {rt} (pf | pt, bhdf) = let
  fun loop {c0:clr}
    {bh0:nat | bh0 <= bh}
    {chld:addr | chld <> null}
    {slf:addr} .<2*bh0+c0>. (
    fpf: rbdiff_v (key, itm, c, c0, bh, bh0, chld, 0(*left*), rt, null, slf)
  , pf0: rbtree_v (key, itm, c0, bh0, 0, slf, chld)
  | pc: ptr (chld), pt: &ptr rt >> ptr rt, p: ptr slf, bhdf: &int? >> int (bh-bh')
  ) :<> #[c':clr;bh':nat;rt:addr
    | c' <= c; bh' <= bh; bh <= bh'+1-c'
  ] [slf:addr | slf <> null] (
    rbnode (key, itm) @ slf, rbtree_v (key, itm, c', bh', 0, null, rt) | ptr slf
  ) = let
    prval B (pf0_clr, pf0_at, pf0_l, pf0_r) = pf0
    prval () = clr_lemma (pf0_clr)
    val pc_l = pc->left
  in
    if pc_l <> null then let
      prval fpf = B1L (pf0_clr, pf0_at, fpf, pf0_r)
    in
      loop (fpf, pf0_l | pc_l, pt, pc, bhdf)
    end else let
      prval E () = pf0_l
      val pc_r = pc->right
      val () = rbtree_parent_set<key,itm> (pf0_r | pc_r, p)
      val c0_r = rbtree_color_get<key,itm> (pf0_r | pc_r)
    in
      if c0_r = RED then let
        val () = rbtree_color_trans_red_blk<key,itm> (pf0_r | pc_r)
        val () = bhdf := 0
        val (pf | pt_new) = balanceRem0<key,itm> (fpf, pf0_r | BLK, pc, 0(*left*), pt, p, pc_r)
        val () = pt := pt_new
      in
        (pf0_at, pf | pc)
      end else let // c0_r = BLK
        val c0 = pc->color
      in
        if c0 = RED then let
          val () = bhdf := 0
          val (pf | pt_new) = balanceRem0<key,itm> (fpf, pf0_r | RED, pc, 0(*left*), pt, p, pc_r)
          val () = pt := pt_new
        in
          (pf0_at, pf | pc)
        end else let
          val (pf | pt_new) = balanceRem1<key,itm> (fpf, pf0_r | BLK, pc, 0(*left*), pt, p, pc_r, bhdf)
          val () = pt := pt_new
        in
          (pf0_at, pf | pc)
        end // end of [if]
      end // end of [if]
    end // end of [if]
  end // end of [loop]
  val pc = pt
in
  loop (E1 (), pf | pc, pt, null, bhdf)
end (* end of [rbtree_remove_min] *)

*)

(* ****** ****** *)

(*

extern
fun{key:t0p;itm:vt0p}
rbtree_remove_max
  {c:clr} {bh:nat} {rt:addr | rt <> null} (
    pf: rbtree_v (key, itm, c, bh, 0, null, rt)
  | pt: &ptr rt >> ptr rt, bhdf: &int? >> int (bh-bh')
  ) :<> #[ 
    c':clr;bh':nat;rt:addr | c' <= c; bh' <= bh; bh <= bh'+1-c'
  ] [slf:addr | slf <> null] (
    rbnode (key, itm) @ slf, rbtree_v (key, itm, c', bh', 0, null, rt) | ptr slf
  )
// end of [rbtree_remove_max]

implement{key,itm}
  rbtree_remove_max {c} {bh} {rt} (pf | pt, bhdf) = let
  fun loop {c0:clr}
    {bh0:nat | bh0 <= bh}
    {chld:addr | chld <> null}
    {slf:addr} .<2*bh0+c0>. (
    fpf: rbdiff_v (key, itm, c, c0, bh, bh0, chld, 1(*right*), rt, null, slf)
  , pf0: rbtree_v (key, itm, c0, bh0, 0, slf, chld)
  | pc: ptr (chld), pt: &ptr rt >> ptr rt, p: ptr slf, bhdf: &int? >> int (bh-bh')
  ) :<> #[c':clr;bh':nat;rt:addr
    | c' <= c; bh' <= bh; bh <= bh'+1-c'
  ] [slf:addr | slf <> null] (
    rbnode (key, itm) @ slf, rbtree_v (key, itm, c', bh', 0, null, rt) | ptr slf
  ) = let
    prval B (pf0_clr, pf0_at, pf0_l, pf0_r) = pf0
    prval () = clr_lemma (pf0_clr)
    val pc_r = pc->right
  in
    if pc_r <> null then let
      prval fpf = B1R (pf0_clr, pf0_at, pf0_l, fpf)
    in
      loop (fpf, pf0_r | pc_r, pt, pc, bhdf)
    end else let
      prval E () = pf0_r
      val pc_l = pc->left
      val () = rbtree_parent_set<key,itm> (pf0_l | pc_l, p)
      val c0_l = rbtree_color_get<key,itm> (pf0_l | pc_l)
    in
      if c0_l = RED then let
        val () = rbtree_color_trans_red_blk<key,itm> (pf0_l | pc_l)
        val () = bhdf := 0
        val (pf | pt_new) = balanceRem0<key,itm> (fpf, pf0_l | BLK, pc, 1(*right*), pt, p, pc_l)
        val () = pt := pt_new
      in
        (pf0_at, pf | pc)
      end else let // c0_l = BLK
        val c0 = pc->color
      in
        if c0 = RED then let
          val () = bhdf := 0
          val (pf | pt_new) = balanceRem0<key,itm> (fpf, pf0_l | RED, pc, 1(*right*), pt, p, pc_l)
          val () = pt := pt_new
        in
          (pf0_at, pf | pc)
        end else let
          val (pf | pt_new) = balanceRem1<key,itm> (fpf, pf0_l | BLK, pc, 1(*right*), pt, p, pc_l, bhdf)
          val () = pt := pt_new
        in
          (pf0_at, pf | pc)
        end // end of [if]
      end // end of [if]
    end // end of [if]
  end // end of [loop]
  val pc = pt
in
  loop (E1 (), pf | pc, pt, null, bhdf)
end (* end of [rbtree_remove_max] *)

*)

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p} rbtree_rbtree_join
  {c,c_l,c_r:clr}
  {bh:nat} {lft,rgh,pnt1,pnt2:addr} (
    pf_clr: clr_p (c, c_l, c_r, 0)
  , pf_l: rbtree_v (key, itm, c_l, bh, 0, pnt1, lft)
  , pf_r: rbtree_v (key, itm, c_r, bh, 0, pnt2, rgh)
  | c: int c, p_l: ptr lft, p_r: ptr rgh, bhdf: &int? >> int (bh+1-c-bh')
  ) :<> #[c':clr;bh':nat | c' <= c; bh' <= bh+1-c; bh+1-c <= bh'+1-c']
    [pnt,slf:addr] (rbtree_v (key, itm, c', bh', 0, pnt, slf) | ptr slf)
// end of [rbtree_rbtree_join]

implement{key,itm} rbtree_rbtree_join
  {c,c_l,c_r} {bh} {lft,rgh,pnt1,pnt2}
  (pf_clr, pf_l, pf_r | c, p_l, p_r, bhdf) = let
  prval () = clr_lemma (pf_clr)
//
  viewtypedef rbnode
    (key:t@ype,itm:viewt@ype,lft:addr) =
    [c:clr;rgh,pnt:addr] rbnode (key, itm, c, lft, rgh, pnt)
  (* end of [viewtypedef rbnode] *)
//
  fun loop {c0:clr}
    {bh0:nat | bh0 <= bh}
    {chld:addr | chld <> null} {rt:addr}
    {slf:addr} .<2*bh0+c0>. (
    fpf: rbdiff_v (key, itm, c_l, c0, bh, bh0, chld, 1(*right*), rt, null, slf)
  , pf0: rbtree_v (key, itm, c0, bh0, 0, slf, chld)
  | pc: ptr (chld), pt: ptr rt, p: ptr slf, bhdf: &int? >> int (bh-bh1)
  ) :<> #[c_l1:clr;bh1:nat
    | c_l1 <= c_l; bh1 <= bh; bh <= bh1+1-c_l1
    ] [slf:addr | slf <> null] [lft,pnt:addr]  (
    rbnode (key, itm, lft) @ slf, rbtree_v (key, itm, c_l1, bh1, 0, slf, lft) | ptr slf
  ) = let
    prval B (pf0_clr, pf0_at, pf0_l, pf0_r) = pf0
    prval () = clr_lemma (pf0_clr)
    val pc_r = pc->right
  in
    if pc_r <> null then let
      prval fpf = B1R {key,itm} (pf0_clr, pf0_at, pf0_l, fpf)
    in
      loop (fpf, pf0_r | pc_r, pt, pc, bhdf)
    end else let
      prval E () = pf0_r
      val pc_l = pc->left
      val () = rbtree_parent_set<key,itm> (pf0_l | pc_l, p)
      val c0_l = rbtree_color_get<key,itm> (pf0_l | pc_l)
    in
      if c0_l = RED then let
        val () = rbtree_color_trans_red_blk<key,itm> (pf0_l | pc_l)
        val () = bhdf := 0
        val (pf | pt) = balanceRem0<key,itm> (fpf, pf0_l | BLK, pc, 1(*right*), pt, p, pc_l)
        val () = pc->left := pt
        val () = rbtree_parent_set<key,itm> (pf | pt, pc)
      in
        (pf0_at, pf | pc)
      end else let // c0_l = BLK
        val c0 = pc->color
      in
        if c0 = RED then let
          val () = bhdf := 0
          val (pf | pt) = balanceRem0<key,itm> (fpf, pf0_l | RED, pc, 1(*right*), pt, p, pc_l)
          val () = pc->left := pt
          val () = rbtree_parent_set<key,itm> (pf | pt, pc)
        in
          (pf0_at, pf | pc)
        end else let
          val (pf | pt) = balanceRem1<key,itm> (fpf, pf0_l | BLK, pc, 1(*right*), pt, p, pc_l, bhdf)
          val () = pc->left := pt
          val () = rbtree_parent_set<key,itm> (pf | pt, pc)
        in
          (pf0_at, pf | pc)
        end // end of [if]
      end // end of [if]
    end // end of [if]
  end // end of [loop]
in
  if p_l <> null then let
    prval fpf = E1 ()
    val c_l = rbtree_color_get (pf_l | p_l)
    val () = rbtree_parent_set (pf_l | p_l, null)
    val (pf_at, pf_l | p_at) = loop (fpf, pf_l | p_l, p_l, null, bhdf)
    val () = p_at->parent := null
    val () = p_at->color := c
    val () = p_at->right := p_r
    val () = rbtree_parent_set<key,itm> (pf_r | p_r, p_at)
    val p_l = p_at->left
    prval fpf = B1L {key,itm} (pf_clr, pf_at, E1 {..} {c} {bh+1-c} {..} {0} (), pf_r)
  in
    if bhdf = 0 then let
    in
      balanceRem0<key,itm> (fpf, pf_l | c_l, p_l, 0(*left*), p_at, p_at, p_l)
    end else let // bhdf > 0
    in
      balanceRem1<key,itm> (fpf, pf_l | c_l, p_l, 0(*left*), p_at, p_at, p_l, bhdf)
    end // end of [if]
  end else let
    prval E () = pf_l
    val c_r = rbtree_color_get (pf_r | p_r)
  in
    if c_r = RED then let
      val () = bhdf := 0
      val () = rbtree_color_trans_red_blk<key,itm> (pf_r | p_r)
    in
      (pf_r | p_r)
    end else let // c_r = BLK
      val () = bhdf := 1-c
    in
      (pf_r | p_r)
    end // end of [if]
  end // end of [if]
end (* end of [rbtree_rbtree_join] *)

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p}
linmap_remove {l_at:addr} (
    m: &map_vt (key, itm), k0: key, cmp: cmp key
  ) :<> [l_at:addr] (
    option_v (rbnode (key, itm) @ l_at, l_at <> null) | ptr l_at
  )
// end of [linmap_remove]

implement{key,itm}
  linmap_remove {l_at} (m, k0, cmp) = let
(*
  val () = $effmask_all begin
    print "linmap_remove: m=\n"; print_linmap (m); print_newline ()
  end // end of [val]
*)
  val pt = m.1
  var p = pt
  var dir: int = 0
  val [c0:int,bh0:int,chld:addr]
    (fpf, pf0 | pc0) = rbtree_split (m.0 | p, k0, dir, cmp)
  // end of [val]
  viewdef V = rbnode (key,itm) @ chld
in
  if pc0 <> null then let
    prval B (pf0_clr, pf0_at, pf0_l, pf0_r) = pf0
    prval () = clr_lemma (pf0_clr)
    val c0 = pc0->color
    var bhdf : int // uninitalized
    val (pf0 | pc0_new) = rbtree_rbtree_join<key,itm>
      (pf0_clr, pf0_l, pf0_r | pc0->color, pc0->left, pc0->right, bhdf)
    // end of [val]
    val () = rbtree_parent_set (pf0 | pc0_new, p)
  in
    if bhdf = 0 then let
      val (pf_new | pt_new) =
        balanceRem0<key,itm> (fpf, pf0 | c0, pc0, dir, pt, p, pc0_new)
      // end of [val]
    in
      m.0 := pf_new; m.1 := pt_new; (Some_v {V} (pf0_at) | pc0) // removal
    end else let
      val (pf_new | pt_new) =
        balanceRem1<key,itm> (fpf, pf0 | c0, pc0, dir, pt, p, pc0_new, bhdf)
      // end of [val]
    in
      m.0 := pf_new; m.1 := pt_new; (Some_v {V} (pf0_at) | pc0) // removal
    end // end of [if]
  end else let
    prval pf = rbdiff_rbtree_join {key,itm} (fpf, pf0)
  in
    m.0 := pf; (None_v {V} () | null) // no removal is performed
  end // end of [if]
end (* end of [linmap_remove] *)

(* ****** ****** *)

// infix order foreach
fun{key:t0p;itm:vt0p} rbtree_foreach_inf
  {v:view} {vt:viewtype}
  {c:clr} {bh:nat} {pnt,slf:addr} {f:eff} .<2*bh+c>. (
    pf1: !rbtree_v (key,itm,c,bh,0,pnt,slf)
  , pf2: !v
  | p: ptr slf
  , f: (!v | key, &itm, !vt) -<f> void
  , env: !vt
  ) :<f> void = let
in
  if p <> null then let
    prval B (pf1_clr, pf1_at, pf1_l, pf1_r) = pf1
    prval () = clr_lemma (pf1_clr)
    val () = rbtree_foreach_inf (pf1_l, pf2 | p->left, f, env)
    val () = f (pf2 | p->key, p->itm, env)
    val () = rbtree_foreach_inf (pf1_r, pf2 | p->right, f, env)
    prval () = pf1 := B (pf1_clr, pf1_at, pf1_l, pf1_r)
  in
    // nothing
  end // end of [if]
end // end of [bst_foreach_inf]

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
  val () = rbtree_foreach_inf<key,itm> {V} {ptr l_f} (m.0, pf | m.1, app, p_f)
  prval () = (pf1 := pf.0; view@ f := pf.1)
in
  // empty
end // end of [linmap_foreach_clo]

(* ****** ****** *)

(*

// for the purpose of debugging

extern
fun{key:t0p;itm:vt0p}
print_rbtree {c:clr} {bh:nat} {v:nat} {pnt,slf:addr}
  (pf: !rbtree_v (key,itm,c,bh,v,pnt,slf) | p: ptr slf): void
  = "print_rbtree"

extern
fun{key:t0p;itm:vt0p}
print_rbtree_dummy {slf:addr} (p: ptr slf): void
  = "print_rbtree"

extern fun{key:t0p;itm:vt0p} print_linmap (map: !map_vt (key,itm)): void

implement{key,itm} print_linmap (map) = print_rbtree (map.0 | map.1)

*)

(* ****** ****** *)

(* end of [linmap_rbtree_ngc.dats] *)
