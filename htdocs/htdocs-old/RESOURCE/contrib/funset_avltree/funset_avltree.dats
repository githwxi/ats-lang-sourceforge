(*
**
** An implementation of functional sets based on AVL trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

abstype set_t (elt: t@ype+)

(* ****** ****** *)

typedef cmp (elt:t@ype) = (elt, elt) -<cloref> Sgn

extern fun{elt:t@ype}
  compare_elt_elt (x1: elt, x2: elt, cmp: cmp elt):<> Sgn

implement{elt} compare_elt_elt (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

extern fun{} funset_empty {elt:t@ype} ():<> set_t (elt)
extern fun{elt:t@ype} funset_singleton (x0: elt):<> set_t (elt)

(* ****** ****** *)

extern fun{} funset_is_empty {elt:t@ype} (xs: set_t elt):<> bool
extern fun{} funset_isnot_empty {elt:t@ype} (xs: set_t elt):<> bool

(* ****** ****** *)

// the time complexity of this function is O(n), where n is the size
extern fun{elt:t@ype} funset_size (xs: set_t elt):<> Nat // of the set

(*
// this function returns the height of the AVL tree representing [xs]
// it is mainly for testing purpose
extern fun{elt:t@ype} funset_height (xs: set_t elt):<> Nat
*)

(* ****** ****** *)

extern fun{elt:t@ype} funset_is_member
  (xs: set_t elt, x0: elt, cmp: cmp elt):<> bool

extern fun{elt:t@ype} funset_isnot_member
  (xs: set_t elt, x0: elt, cmp: cmp elt):<> bool

extern fun{elt:t@ype} funset_insert
  (xs: set_t elt, x0: elt, cmp: cmp elt):<> set_t (elt)

extern fun{elt:t@ype} funset_remove
  (xs: set_t elt, x0: elt, cmp: cmp elt):<> set_t (elt)

extern fun{elt:t@ype} funset_choose (xs: set_t elt):<> Option_vt (elt)

extern fun{elt:t@ype} funset_union
  (xs1: set_t elt, xs2: set_t elt, cmp: cmp elt):<> set_t (elt)

extern fun{elt:t@ype} funset_intersect
  (xs1: set_t elt, xs2: set_t elt, cmp: cmp elt):<> set_t (elt)

extern fun{elt:t@ype} funset_diff
  (xs1: set_t elt, xs2: set_t elt, cmp: cmp elt):<> set_t (elt)

// computing the symmetric difference between two given sets
extern fun{elt:t@ype} funset_symmdiff
  (xs1: set_t elt, xs2: set_t elt, cmp: cmp elt):<> set_t (elt)

(* ****** ****** *)

extern fun{elt:t@ype} funset_is_subset
  (xs1: set_t elt, xs2: set_t elt, cmp: cmp elt):<> bool

extern fun{elt:t@ype} funset_is_equal
  (xs1: set_t elt, xs2: set_t elt, cmp: cmp elt):<> bool

(* ****** ****** *)

extern fun{elt:t@ype} funset_foreach_clo {v:view}
  (pf: !v | xs: set_t elt, f: &(!v | elt) -<clo> void):<> void

extern fun{elt:t@ype} funset_foreach_cloref
  (xs: set_t elt, f: (elt) -<cloref> void):<!ref> void

(* ****** ****** *)

extern fun{elt:t@ype}
  funset_make_list (xs: List elt, cmp: cmp elt):<> set_t (elt)
// end of [extern]

(* ****** ****** *)

datatype avltree (elt:t@ype+, int(*height*), int(*size*)) =
  | {hl,hr:nat | hl <= hr+1; hr <= hl+1} {sl,sr:nat}
    B (elt, max(hl,hr)+1, sl+sr+1) of
      (int (max(hl,hr)+1), avltree (elt, hl, sl), elt, avltree (elt, hr, sr))
  | E (elt, 0, 0)

typedef avltree_inc (elt:t@ype, h:int, s:int) =
  [h1:nat | h <= h1; h1 <= h+1] avltree (elt, h1, s)

typedef avltree_dec (elt:t@ype, h:int, s:int) =
  [h1:nat | h1 <= h; h <= h1+1] avltree (elt, h1, s)

(* ****** ****** *)

assume set_t (elt:t@ype) = [h,s:nat] avltree (elt, h, s)

(* ****** ****** *)

fn{elt:t@ype}
  avltree_height {h,s:nat}
  (t: avltree (elt, h, s)):<> int h = begin
  case+ t of | B (h, _, _, _) => h | E () => 0
end // end of [avltree_height]

(* ****** ****** *)

implement{} funset_empty () = E ()
implement{elt} funset_singleton (x) = B (1, E (), x, E ())

(* ****** ****** *)

implement{} funset_is_empty (t) =
  case+ t of | B _ => false | E => true
// end of [funset_is_empty]

implement{} funset_isnot_empty (t) =
  case+ t of | B _ => true | E => false
// end of [funset_isnot_empty]

(* ****** ****** *)

implement{elt} funset_size (t) = size (t) where {
  fun size {h,s:nat} .<h>.
    (t: avltree (elt, h, s)):<> int s = begin
    case+ t of B (_, tl, _, tr) => 1 + size (tl) + size (tr) | E () => 0
  end // end of [size]
} // end of [funset_size]

(*
implement{elt} funset_height (t) = begin
  case+ t of B (h, _, _, _) => h | E () => 0
end // end of [funset_height]
*)

(* ****** ****** *)

implement{elt} funset_is_member (t, x0, cmp) = mem (t) where {
  fun mem {h,s:nat} .<h>.
    (t: avltree (elt, h, s)):<cloref> bool = case+ t of
    | B (_, tl, x, tr) => let
        val sgn = compare_elt_elt<elt> (x0, x, cmp)
      in
        if sgn < 0 then mem tl else if sgn > 0 then mem tr else true
      end // end of [B]
    | E () => false
  // end of [mem]
} // end of [funset_is_member]

implement{elt} funset_isnot_member (t, x0, cmp) =
  if funset_is_member<elt> (t, x0, cmp) then false else true
// en dof [funset_isnot_member]

(* ****** ****** *)

(*
** left rotation for restoring height invariant
*)
fn{elt:t@ype}
  avltree_lrotate {hl,hr,sl,sr:nat | hl+2 == hr}
  (tl: avltree (elt, hl, sl), x: elt, tr: avltree (elt, hr, sr))
  :<> avltree_inc (elt, hr, sl+sr+1) = let
  val+ B (hr, trl, xr, trr) = tr
  val hrl = avltree_height trl and hrr = avltree_height trr
in
  if hrl <= hrr then begin // hr = 1+hlr
    B (hrl+2, B (hrl+1, tl, x, trl), xr, trr)
  end else let // [hrl > hrr]: deep rotation
    val+ B (_(*hrl*), trll, xrl, trlr) = trl
  in
    B (hr, B (hrl, tl, x, trll), xrl, B (hrl, trlr, xr, trr))
  end // end of [if]
end // end of [avltree_lrotate]

(*
** right rotation for restoring height invariant
*)
fn{elt:t@ype} avltree_rrotate {hl,hr,sl,sr:nat | hl == hr+2}
  (tl: avltree (elt, hl, sl), x: elt, tr: avltree (elt, hr, sr))
  :<> avltree_inc (elt, hl, sl+sr+1) = let
  val+ B (hl, tll, xl, tlr) = tl
  val hll = avltree_height tll and hlr = avltree_height tlr
in
  if hll >= hlr then begin // hl = 1+hll
    B (hlr+2, tll, xl, B (hlr+1, tlr, x, tr))
  end else let // [hll < hlr]: deep rotation
    val+ B (_(*hlr*), tlrl, xlr, tlrr) = tlr
  in
    B (hl, B (hlr, tll, xl, tlrl), xlr, B (hlr, tlrr, x, tr))
  end // end of [if]
end // end of [avltree_rrotate]

(* ****** ****** *)

implement{elt} funset_insert (t, x0, cmp) = let
  fun insert {h,s:nat} .<h>.
    (t: avltree (elt, h, s), inserted: &int? >> int i)
    :<cloref> #[i:two] avltree_inc (elt, h, s+i) = case+ t of
    | B (_(*h*), tl, x, tr) => let
        val sgn = compare_elt_elt<elt> (x0, x, cmp)
      in
        if sgn < 0 then let
          val tl = insert (tl, inserted)
          val hl = avltree_height (tl) and hr = avltree_height (tr)
        in
          if hl - hr <= 1 then begin
            B (max(hl, hr) + 1, tl, x, tr)
          end else begin // hl = hr+2
            avltree_rrotate (tl, x, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val tr = insert (tr, inserted)
          val hl = avltree_height (tl) and hr = avltree_height (tr)
        in
          if hr - hl <= 1 then begin
            B (max(hl, hr)+1, tl, x, tr)
          end else begin // hl+1 = hr
            avltree_lrotate (tl, x, tr)
          end // end of [if]
        end else begin
          inserted := 0;  t // no insertion
        end // end of [if]
      end // end of [B]
    | E () => (inserted := 1; B (1, E (), x0, E ()))
  // end of [insert]
  var inserted: int // uninitialized
in
  insert (t, inserted) // size = size (t) + inserted
end // end of [funset_insert]

(* ****** ****** *)

fun{elt:t@ype}
  avltree_takeout_min {h,s:pos} .<h>.
  (t: avltree (elt, h, s), x0: &elt? >> elt)
  :<> avltree_dec (elt, h, s-1) = let
  val+ B (_, tl, x, tr) = t
in
  case+ tl of
  | B _ => let
      val tl = avltree_takeout_min<elt> (tl, x0)
      val hl = avltree_height (tl) and hr = avltree_height (tr)
    in
      if hr - hl <= 1 then begin
        B (max(hl,hr)+1, tl, x, tr)
      end else begin // hl+2 = hr
       avltree_lrotate (tl, x, tr)
      end // end of [if]
    end // end of [B]
  | E () => (x0 := x; tr)
end // end of [avltree_takeout_min]

(* ****** ****** *)

implement{elt} funset_remove (t, x0, cmp) = let
  fun remove {h,s:nat} .<h>.
    (t: avltree (elt, h, s), removed: &int? >> int i)
    :<cloref> #[i:two | i <= s] avltree_dec (elt, h, s-i) =
    case+ t of
    | B (_(*h*), tl, x, tr) => let
        val sgn = compare_elt_elt<elt> (x0, x, cmp)
      in
        if sgn < 0 then let
          val tl = remove (tl, removed)
          val hl = avltree_height tl and hr = avltree_height tr
        in
          if hr - hl <= 1 then begin
            B (max(hl,hr)+1, tl, x, tr)
          end else begin // hl+2 == hr
            avltree_lrotate (tl, x, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val tr = remove (tr, removed)
          val hl = avltree_height tl and hr = avltree_height tr
        in
          if hl - hr <= 1 then begin
            B (max(hl,hr)+1, tl, x, tr)
          end else begin // hl = hr+2
            avltree_rrotate (tl, x, tr)
          end // end of [if]
        end else let
          val () = removed := 1
        in
          case+ tr of
          | B _ => let
              var x_min: elt
              val tr = avltree_takeout_min<elt> (tr, x_min)
              val hl = avltree_height tl and hr = avltree_height tr
            in
              if hl - hr <= 1 then begin
                B (max(hl,hr)+1, tl, x_min, tr)
              end else begin // hl+2 = hr
                avltree_rrotate (tl, x_min, tr)
              end // end of [if]
            end // end of [B]
          | E () => tl
        end // end of [if]
      end // end of [B]
    | E () => (removed := 0; E ())
  // end of [remove]
  var removed: int // uninitialized
in
  remove (t, removed) // size = size (t) - removed
end // end of [funset_remove]

(* ****** ****** *)

(*
** left join: height(tl) >= height(tr)
*)
fun{elt:t@ype}
  avltree_ljoin {hl,hr,sl,sr:nat | hl >= hr} .<hl>.
  (tl: avltree (elt, hl, sl), x: elt, tr: avltree (elt, hr, sr))
  :<> avltree_inc (elt, hl, sl+sr+1) = let
  val hl = avltree_height (tl) and hr = avltree_height (tr)
in
  if hl - hr >= 2 then let
    val+ B (_, tll, xl, tlr) = tl
    val tlr = avltree_ljoin<elt> (tlr, x, tr)
    val hll = avltree_height (tll) and hlr = avltree_height (tlr)
  in
    if hlr - hll <= 1 then begin
      B (max(hll,hlr)+1, tll, xl, tlr)
    end else begin // hll+2 = hlr
      avltree_lrotate (tll, xl, tlr)
    end // end of [if]
  end else begin
    B (hl+1, tl, x, tr)
  end // end of [if]
end // end of [avltree_ljoin]

(*
** right join: height(tl) <= height(tr)
*)
fun{elt:t@ype}
  avltree_rjoin {hl,hr,sl,sr:nat | hl <= hr} .<hr>.
  (tl: avltree (elt, hl, sl), x: elt, tr: avltree (elt, hr, sr))
  :<> avltree_inc (elt, hr, sl+sr+1) = let
  val hl = avltree_height (tl) and hr = avltree_height (tr)
in
  if hr - hl >= 2 then let
    val+ B (_, trl, xr, trr) = tr
    val trl = avltree_rjoin<elt> (tl, x, trl)
    val hrl = avltree_height (trl) and hrr = avltree_height (trr)
  in
    if hrl - hrr <= 1 then begin
      B (max(hrl,hrr)+1, trl, xr, trr)
    end else begin // hrl = hrr+2
      avltree_rrotate (trl, xr, trr)
    end // end of [if]
  end else begin
    B (hr+1, tl, x, tr)
  end // end of [if]
end // end of [avltree_rjoin]

(* ****** ****** *)

fn{elt:t@ype} avltree_join {hl,hr,sl,sr:nat}
  (tl: avltree (elt, hl, sl), x: elt, tr: avltree (elt, hr, sr))
  :<> [h:int | hl <= h; hr <= h; h <= max(hl,hr)+1] avltree (elt, h, sl+sr+1) = let
  val hl = avltree_height tl and hr = avltree_height tr
in
  if hl >= hr then avltree_ljoin (tl, x, tr) else avltree_rjoin (tl, x, tr)
end // end of [avltree_join]

(* ****** ****** *)

fn{elt:t@ype} avltree_concat {hl,hr,sl,sr:nat}
  (tl: avltree (elt, hl, sl), tr: avltree (elt, hr, sr))
  :<> [h:nat | h <= max(hl,hr)+1] avltree (elt, h, sl+sr) = begin
  case+ (tl, tr) of
  | (E (), _) => tr
  | (_, E ()) => tl
  | (_, _) =>> let
      var x_min: elt // uninitialized
      val tr = avltree_takeout_min<elt> (tr, x_min)
    in
      avltree_join (tl, x_min, tr)
    end // end of [_, _]
end // end of [avltree_concat]

(* ****** ****** *)

typedef avltree = avltree (void, 0, 0)

fun{elt:t@ype}
  avltree_split_at {h,s:nat} .<h>. (
    t: avltree (elt, h, s), x0: elt
  , tl0: &avltree? >> avltree (elt, hl, sl)
  , tr0: &avltree? >> avltree (elt, hr, sr)
  , cmp: cmp elt
  ) :<> #[i:two; hl,hr,sl,sr:nat | hl <= h; hr <= h; sl+sr+i == s] int i =
  case t of
  | B (_(*h*), tl, x, tr) => let
      val sgn = compare_elt_elt<elt> (x0, x, cmp)
    in
      if sgn < 0 then let
        val i = avltree_split_at (tl, x0, tl0, tr0, cmp)
      in
        tr0 := avltree_join (tr0, x, tr); i
      end else if sgn > 0 then let
        val i = avltree_split_at (tr, x0, tl0, tr0, cmp)
      in
        tl0 := avltree_join (tl, x, tl0); i
      end else begin
        tl0 := tl; tr0 := tr; 1 // [x] is found in [t]
      end // end of [if]
    end // end of [B]
  | E () => (tl0 := E (); tr0 := E (); 0)
// end of [avltree_split_at]

(* ****** ****** *)

implement{elt} funset_choose (t) = case+ t of
  | B (_(*h*), _(*tl*), x, _(*tr*)) => Some_vt x | E () => None_vt ()
// end of [funset_choose]

(* ****** ****** *)

implement{elt} funset_union (t1, t2, cmp) = uni (t1, t2) where {
  fun uni {h1,h2,s1,s2:nat} .<h1>.
    (t1: avltree (elt, h1, s1), t2: avltree (elt, h2, s2)):<cloref>
    [h,s:nat | s1 <= s; s2 <= s; s <= s1+s2] avltree (elt, h, s) = begin
    case+ (t1, t2) of
    | (E (), _) => t2 | (_, E ()) => t1 | (_, _) =>> let
        val+ B (_(*h1*), t1l, x1, t1r) = t1
        var t2l0: avltree? and t2r0: avltree?
        val+ i = avltree_split_at (t2, x1, t2l0, t2r0, cmp)
        val t12l = uni (t1l, t2l0) and t12r = uni (t1r, t2r0)
      in
        avltree_join (t12l, x1, t12r)
      end // end of [_, _]
    end // end of [uni]
  // end of [uni] // [union] is a keyword
} // end of [funset_union]

(* ****** ****** *)

implement{elt} funset_intersect (t1, t2, cmp) = inter (t1, t2) where {
  fun inter {h1,h2,s1,s2:nat} .<h1>.
    (t1: avltree (elt, h1, s1), t2: avltree (elt, h2, s2))
    :<cloref> [h,s:nat | s <= s1; s <= s2] avltree (elt, h, s) =
    begin case+ (t1, t2) of
    | (E (), _) => E () | (_, E ()) => E () | (_, _) =>> let
        val+ B (_(*h1*), t1l, x1, t1r) = t1
        var t2l0: avltree? and t2r0: avltree?
        val+ i = avltree_split_at (t2, x1, t2l0, t2r0, cmp)
        val t12l = inter (t1l, t2l0) and t12r = inter (t1r, t2r0)
      in
        if i = 0 then avltree_concat (t12l, t12r) else avltree_join (t12l, x1, t12r)
      end // end of [_, _]
    end // end of [inter]
  // end of [inter]
} // end of [funset_intersect]

(* ****** ****** *)

implement{elt} funset_diff (t1, t2, cmp) = diff (t1, t2) where {
  fun diff {h1,h2,s1,s2:nat} .<h1>.
    (t1: avltree (elt, h1, s1), t2: avltree (elt, h2, s2)):<cloref>
    [h,s:nat | s <= s1] avltree (elt, h, s) = begin case+ (t1, t2) of
    | (E (), _) => E () | (_, E ()) => t1 | (_, _) =>> let
        val+ B (_(*h1*), t1l, x1, t1r) = t1
        var t2l0: avltree? and t2r0: avltree?
        val+ i = avltree_split_at (t2, x1, t2l0, t2r0, cmp)
        val t12l = diff (t1l, t2l0) and t12r = diff (t1r, t2r0)
      in
        if i > 0 then avltree_concat (t12l, t12r) else avltree_join (t12l, x1, t12r)
      end // end of [_, _]
    end // end of [diff]
  // end of [diff]
} // end of [funset_diff]

(* ****** ****** *)

implement{elt} funset_symmdiff (t1, t2, cmp) = symmdiff (t1, t2) where {
  fun symmdiff {h1,h2,s1,s2:nat} .<h1>.
    (t1: avltree (elt, h1, s1), t2: avltree (elt, h2, s2)):<cloref>
    [h,s:nat | s <= s1+s2] avltree (elt, h, s) = begin case+ (t1, t2) of
    | (E (), _) => t2 | (_, E ()) => t1 | (_, _) =>> let
        val+ B (_(*h1*), t1l, x1, t1r) = t1
        var t2l0: avltree? and t2r0: avltree?
        val+ i = avltree_split_at (t2, x1, t2l0, t2r0, cmp)
        val t12l = symmdiff (t1l, t2l0) and t12r = symmdiff (t1r, t2r0)
      in
        if i > 0 then avltree_concat (t12l, t12r) else avltree_join (t12l, x1, t12r)
      end // end of [_, _]
    end // end of [symmdiff]
  // end of [diff]
} // end of [funset_symmdiff]

(* ****** ****** *)

implement{elt} funset_is_subset (t1, t2, cmp) = test (t1, t2) where {
  fun test {h1,h2,s1,s2:nat} .<h1>. (
      t1: avltree (elt, h1, s1), t2: avltree (elt, h2, s2)
    ) :<cloref> bool = begin case+ (t1, t2) of
    | (E (), _) => true | (_, E ()) => false | (_, _) =>> let
        val+ B(_(*h1*), t1l, x1, t1r) = t1
        var t2l0: avltree? and t2r0: avltree?
        val+ i = avltree_split_at (t2, x1, t2l0, t2r0, cmp)
      in
        if i > 0 then
          (test (t1l, t2l0) andalso test (t1r, t2r0))
        else false
      end // end of [_, _]
  end // end of [test]    
} // end of [funset_is_subset]

implement{elt} funset_is_equal (t1, t2, cmp) =
  if funset_is_subset<elt> (t1, t2, cmp) then
    funset_is_subset<elt> (t2, t1, cmp) else false
  // end of [if]
(* end of [funset_is_equal] *)

(* ****** ****** *)

// infix order traversal
implement{elt} funset_foreach_clo
  {v} (pf | t, f) = aux (pf | f, t) where {
  viewtypedef clo_type = (!v | elt) -<clo> void
  fun aux {h,s:nat} .<h>.
    (pf: !v | f: &clo_type, t: avltree (elt, h, s))
    :<> void = begin case+ t of
    | B (_(*h*), tl, x, tr) => begin (* inorder traversal *)
        aux (pf | f, tl); f (pf | x); aux (pf | f, tr)
      end // end of [B]
    | E () => ()
  end // end of [aux]
} // end of [funset_foreach_clo]

// infix order traversal
implement{elt}
  funset_foreach_cloref (t, f) = let
  val f = __cast (f) where { extern castfn __cast
    (f: (elt) -<cloref> void):<> (!unit_v | elt) -<cloref> void
  } // end of [val]
  typedef clo_type = (!unit_v | elt) -<clo> void
  val (vbox pf_f | p_f) = cloref_get_view_ptr {clo_type} (f)
  prval pf = unit_v ()
  val () = funset_foreach_clo<elt> {unit_v} (pf | t, !p_f)
  prval unit_v () = pf
in
  // empty
end // end of [funset_foreach_cloref]

(* ****** ****** *)

implement{elt}
  funset_make_list (xs, cmp) = loop (xs, funset_empty ()) where {
  typedef res_t = set_t (elt)
  fun loop {n:nat} .<n>.
    (xs:  list (elt, n), res: res_t):<cloref> res_t = case+ xs of
    | list_cons (x, xs) => loop (xs, funset_insert (res, x, cmp))
    | list_nil () => res
} // end of [funset_make_list]

(* ****** ****** *)

(* end of [funset_avltree.dats] *)
