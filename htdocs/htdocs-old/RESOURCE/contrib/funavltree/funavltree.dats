(*
**
** An implementation of functional arrays based on Braun trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

// Various operations on AVL trees are implemented here. Note that these
// operations may need to be modified when sets, multisets and associative
// maps are implemented based on AVL trees.

(* ****** ****** *)

typedef cmp (elt:t@ype) = (elt, elt) -> bool
extern fun{elt:t@ype} compare_elt_elt (x1: elt, x2: elt, cmp: cmp elt): Sgn

datatype avltree (elt:t@ype+, int(*height*)) =
  | {hl,hr:nat | hl <= hr+1; hr <= hl+1}
    B (elt, max(hl,hr)+1) of
      (int (max(hl,hr)+1), avltree (elt, hl), elt, avltree (elt, hr))
  | E (elt, 0)

(* ****** ****** *)

fn{elt:t@ype} avltree_height {h:nat}
  (t: avltree (elt, h)): int h = begin
  case+ t of | B (h, _, _, _) => h | E () => 0
end // end of [avltree_height]

(* ****** ****** *)

extern fun{elt:t@ype} avltree_member
  {h:nat} (t: avltree (elt, h), x0: elt, cmp: cmp elt): bool

implement{elt} avltree_member (t, x0, cmp) = member (t) where {
  fun member {h:nat} (t: avltree (elt, h)): bool = case+ t of
    | B (_, tl, x, tr) => let
        val sgn = compare_elt_elt (x0, x, cmp)
      in
        if sgn < 0 then member tl else if sgn > 0 then member tr else true
      end // end of [B]
    | E () => false
} // end of [avltree_member]

(* ****** ****** *)

(*
** left rotation for restoring height invariant
*)
fn{elt:t@ype} avltree_lrotate {hl,hr:nat | hl+2 == hr}
  (tl: avltree (elt, hl), x: elt, tr: avltree (elt, hr))
  : [h:nat | hr <= h; h <= hr+1] avltree (elt, h) = let
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
fn{elt:t@ype} avltree_rrotate {hl,hr:nat | hl == hr+2}
  (tl: avltree (elt, hl), x: elt, tr: avltree (elt, hr))
  : [h:nat | hl <= h; h <= hl+1] avltree (elt, h) = let
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

exception ElementFoundException of ()

extern fun{elt:t@ype} avltree_insert
  {h:nat} (t: avltree (elt, h), x0: elt, cmp: cmp elt)
  : [h1: nat | h <= h1; h1 <= h+1] avltree (elt, h1)

implement{elt} avltree_insert (t, x0, cmp) = let
  fun ins {h:nat} (t: avltree (elt, h), inserted: &int? >> int)
    :<cloref1> [h1: nat | h <= h1; h1 <= h+1] avltree (elt, h1) = begin case+ t of
    | B (_(*h*), tl, x, tr) => let
        val sgn = compare_elt_elt (x0, x, cmp)
      in
        if sgn < 0 then let
          val tl = ins (tl, inserted)
          val hl = avltree_height (tl) and hr = avltree_height (tr)
        in
          if hl - hr <= 1 then begin
            B (max(hl, hr) + 1, tl, x, tr)
          end else begin // hl = hr+2
            avltree_rrotate (tl, x, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val tr = ins (tr, inserted)
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
  end // end of [ins]
  var inserted: int // uninitialized
  val t1 = ins (t, inserted) // size (t1) = 1 + size (t) - inserted
  val () = if inserted = 0 then $raise ElementFoundException ()
in
  t1 // size (t1) = 1 + size (t)
end // end of [avltree_insert]

(* ****** ****** *)

fun{elt:t@ype} avltree_takeout_min {h:pos}
  (t: avltree (elt, h), x0: &elt? >> elt)
  : [h1:nat | h1 <= h; h <= h1+1] avltree (elt, h1) = let
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

exception ElementNotFoundException of ()

extern fun{elt:t@ype} avltree_remove
  {h:nat} (t: avltree (elt, h), x0: elt, cmp: cmp elt)
  : [h1:nat | h1 <= h; h <= h1+1] avltree (elt, h1)

implement{elt} avltree_remove (t, x0, cmp) = let
  var removed: int // uninitialized
  fun rmv {h:nat} (t: avltree (elt, h), removed: &int? >> int)
    :<cloref1> [h1:nat | h1 <= h; h <= h1+1] avltree (elt, h1) = begin
    case+ t of
    | B (_(*h*), tl, x, tr) => let
        val sgn = compare_elt_elt (x0, x, cmp)
      in
        if sgn < 0 then let
          val tl = rmv (tl, removed)
          val hl = avltree_height tl and hr = avltree_height tr
        in
          if hr - hl <= 1 then begin
            B (max(hl,hr)+1, tl, x, tr)
          end else begin // hl+2 == hr
            avltree_lrotate (tl, x, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val tr = rmv (tr, removed)
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
          case+ tl of
          | B _ => let
              var x_min: elt
              val tl = avltree_takeout_min<elt> (tl, x_min)
              val hl = avltree_height tl and hr = avltree_height tr
            in
              if hr - hl <= 1 then begin
                B (max(hl,hr)+1, tl, x_min, tr)
              end else begin // hl+2 = hr
                avltree_lrotate (tl, x_min, tr)
              end // end of [if]
            end // end of [B]
          | E () => tr
        end // end of [if]
      end // end of [B]
    | E () => (removed := 0; E ())
  end // end of [rmv]
  val t1 = rmv (t, removed)
  val () = if removed = 0 then $raise ElementNotFoundException ()
in
  t1 // size (t1) = size (t) - 1
end // end of [avltree_remove]

(* ****** ****** *)

(*
** left join: height(tl) >= height(tr)
*)
fun{elt:t@ype} avltree_ljoin {hl,hr:nat | hl >= hr}
  (tl: avltree (elt, hl), x: elt, tr: avltree (elt, hr))
  : [h:int | hl <= h; h <= hl+1] avltree (elt, h) = let
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
fun{elt:t@ype} avltree_rjoin {hl,hr:nat | hl <= hr}
  (tl: avltree (elt, hl), x: elt, tr: avltree (elt, hr))
  : [h:int | hr <= h; h <= hr+1] avltree (elt, h) = let
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

(* end of [funavltree.dats] *)
