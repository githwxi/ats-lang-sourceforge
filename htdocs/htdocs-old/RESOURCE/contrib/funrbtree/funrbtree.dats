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

(*
** A red-black tree implementation
**
** The insertion operation is based on the algorithm in the following
** paper by Chris Okasaki:
**
** Red-Black Trees in a Functional Setting (Functional Pearls)
**
** J. of Functional Programming, vol. 9 (4), pp. 471-477, January, 1993
**
** The removal operation, which seems novel in its implementation, is by
** Hongwei Xi
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

extern fun{a:t@ype} print_elt (x: a): void // for debugging

(* ****** ****** *)

typedef cmp (a: t@ype) = (a, a) -<cloref> Sgn
extern fun{a:t@ype} compare_elt_elt (x1: a, x2: a, cmp: cmp a):<> Sgn

implement{elt} compare_elt_elt (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

#define BLK 0; #define RED 1
sortdef clr = {c:nat | c < 2}
typedef color = [c:clr] int c

(* ****** ****** *)

datatype rbtree (
  elt:t@ype, int(*color*), int(*blackheight*), int(*violation*)
) =
  | E (elt, BLK, 0, 0)
  | {c,c1,c2:clr} {bh:nat} {v:int}
      {c == BLK && v == 0 || c == RED && v == c1+c2}
    T (elt, c, bh+1-c, v) of (int c, rbtree0 (elt, c1, bh), elt, rbtree0 (elt, c2, bh))

// rbtree0: for trees of no violations
where rbtree0 (elt:t@ype,c:int,bh:int) = rbtree (elt, c, bh, 0(*vio*))

(* ****** ****** *)

extern fun{} rbtree_nil
  {elt:t@ype} (): rbtree0 (elt, 0, 0) // always inline
extern fun{elt:t@ype} rbtree_black_height
  {c:clr} {bh:nat} {v:int} (t: rbtree (elt, c, bh, v)): int bh
extern fun{elt:t@ype} rbtree_size
  {c:clr} {bh:nat} {v:int} (t: rbtree (elt, c, bh, v)): Nat

implement{} rbtree_nil () = E ()

implement{elt} rbtree_black_height (t) = loop (t, 0) where {
  fun loop {c:clr} {bh:nat} {v:int} {r:nat}
    (t: rbtree (elt, c, bh, v), res: int r): int (r+bh) =
    case+ t of T (c, tl, _, _) => loop (tl, res+1-c) | E () => res
} // end of [rbtree_black_right]

implement{elt} rbtree_size (t) = aux t where {
  fun aux {c:clr} {bh:nat} {v:int}
    (t: rbtree (elt, c, bh, v)): Nat = begin case+ t of
    | T (_, tl, _, tr) => 1 + rbtree_size (tl) + rbtree_size (tr)
    | E () => 0
  end // end of [aux]
} // end of [rbtree_size]

(* ****** ****** *)

typedef set_t (elt:t@ype) = [c:clr;bh:nat] rbtree0 (elt, c, bh)

(* ****** ****** *)

extern fun{elt:t@ype} print_rbtree
  {c:clr} {bh:nat} {v:int} (t: rbtree (elt, c, bh, v)): void

implement{elt} print_rbtree (t) = aux (2 * bh, t) where {
  val bh = rbtree_black_height (t)
  fun indent (n: int): void =
    if n > 0 then (print_char ' '; indent (n-1)) else ()
  // end of [indent]
  fun aux {c:clr} {bh:nat} {v:int}
    (n: int, t: rbtree (elt, c, bh, v)): void = case+ t of
    | T (c, tl, x, tr) => () where {
        val () = aux (n-1, tl)
        val () = indent (n)
        val () = if c = 0 then print_string "B:" else print_string "R:"
        val () = print_elt (x)
        val () = print_newline ()
        val () = aux (n-1, tr)
      } // end of [T]
(*
    | E () => (indent n; print_char 'E'; print_newline ())
*)
    | E () => ()
  // end of [aux]
} // end of [print_rbtree]

(* ****** ****** *)

extern fun{elt:t@ype} rbtree_member
  {c:clr} {bh:nat} (t: rbtree0 (elt, c, bh), x0: elt, cmp: cmp elt): bool
// end of [rbtree_member]

implement{elt} rbtree_member (t, x0, cmp) = aux (t) where {
  fun aux {c:clr} {bh: nat}
    (t: rbtree0 (elt, c, bh)):<cloref1> bool = case+ t of
    | T (_, t1, x, t2) => let
        val sgn = compare_elt_elt (x0, x, cmp)
      in
        if sgn < 0 then aux t1 else if sgn > 0 then aux t2 else true
      end // end of [T]
    | E () => false
} // end of [rbtree_member]

(* ****** ****** *)

fn{elt:t@ype} balinc_l // right rotatio
  {c1,c2:clr} {bh:nat} {v:nat}
  (t1: rbtree (elt, c1, bh, v), x: elt, t2: rbtree (elt, c2, bh, 0))
  :<> [c:clr] rbtree0 (elt, c, bh+1) = let
  #define B BLK; #define R RED
in
  case+ (t1, x, t2) of
  | (T (R, T (R, a, x, b), y, c), z, d) => T (R, T (B, a, x, b), y, T (B, c, z, d))
  | (T (R, a, x, T (R, b, y, c)), z, d) => T (R, T (B, a, x, b), y, T (B, c, z, d))
  | (a, x, b) =>> T (B, a, x, b)
end // end of [balinc_l]

fn{elt:t@ype} balinc_r // left rotation
  {c1,c2:clr} {bh:nat} {v:nat}
  (t1: rbtree (elt, c1, bh, 0), x: elt, t2: rbtree (elt, c2, bh, v))
  :<> [c:clr] rbtree0 (elt, c, bh+1) = let
  #define B BLK; #define R RED
in
  case+ (t1, x, t2) of
  | (a, x, T (R, T (R, b, y, c), z, d)) => T (R, T (B, a, x, b), y, T (B, c, z, d))
  | (a, x, T (R, b, y, T (R, c, z, d))) => T (R, T (B, a, x, b), y, T (B, c, z, d))
  | (a, x, b) =>> T (B, a, x, b)
end // end of [balinc_r]

(* ****** ****** *)

extern fun{elt:t@ype} rbtree_insert
  {c:clr} {bh:nat} ( // tag = 0/1 : inserted / not inserted
    t: rbtree0 (elt, c, bh), x: elt, tag: &int? >> int, cmp: cmp elt
  ) :<> [bh1:nat] rbtree0 (elt, 0(*black*), bh1)

implement{elt} rbtree_insert (t, x0, tag, cmp) = let
  fun ins {c:clr} {bh:nat} .<bh,c>. (
      t: rbtree0 (elt, c, bh), x0: elt, tag: &int? >> int
    ) :<cloref> [c1:clr][v:nat | v <= c] rbtree (elt, c1, bh, v) =
    case+ t of
    | T (c, t1, x, t2) => let
        val sgn = compare_elt_elt (x0, x, cmp)
      in
        case+ sgn of
        | ~1 (* x0 < x *) => let
            val [c1:int] t1 = ins (t1, x0, tag) in
            if c = BLK then balinc_l (t1, x, t2) else T {..}{..}{..}{c1} (RED, t1, x, t2)
          end // end of [~1]
        |  1 (* x0 > x *) => let
            val [c1:int] t2 = ins (t2, x0, tag) in
            if c = BLK then balinc_r (t1, x, t2) else T {..}{..}{..}{c1} (RED, t1, x, t2)
        end // end of [ 1]
      |  _ (* x0 = x *) => (tag := 1; t) // no insertion
      end // end of [T]
    | E () => (tag := 0; T {..}{..}{..}{0} (RED, E, x0, E))
  // end of [ins]
  val t = ins (t, x0, tag)
in
  case+ t of T (RED, t1, x, t2) => T (BLK, t1, x, t2) | _ =>> t
end // end of [rbtree_insert]

(* ****** ****** *)

fn{elt:t@ype} rbtree_clr_trans_red_blk {bh:nat} {v:int}
  (t: rbtree (elt, RED, bh, v)):<> rbtree (elt, BLK, bh+1, 0) = let
  val+ T (RED, t1, x, t2) = t in T (BLK, t1, x, t2)
end // end of [rbtree_clr_trans_red_blk]

fn{elt:t@ype} rbtree_clr_trans_blk_red
  {bh:pos} (t: rbtree (elt, BLK, bh, 0))
  :<> [v:nat] rbtree (elt, RED, bh-1, v) = let
  val+ T {..}{c,c1,c2} (BLK, t1, x, t2) = t in T {..}{..}{..}{c1+c2} (RED, t1, x, t2)
end // end of [rbtree_clr_trans_blk_red]

(* ****** ****** *)

fn{elt:t@ype} balrem_l
  {c1,c2:clr} {bh:nat} {v:nat} (
    t1: rbtree (elt, c1, bh, v)
  , x: elt
  , t2: rbtree0 (elt, c2, bh+1)
  ) :<> [c:clr;v:nat | v <= c2] rbtree (elt, c, bh+1, v) = let
(*
** // nothing
*)
in
  case+ t1 of
  | T (RED, t1l, x1, t1r) =>
      T {..}{..}{..}{c2} (RED, T (BLK, t1l, x1, t1r), x, t2)
    // end of [T (RED, ...)]
  | _ =>> begin case+ t2 of
      | T {..} {c2,c2l,c2r} (BLK, t2l, x2, t2r) =>
          balinc_r (t1, x, T {..}{..}{..}{c2l+c2r} (RED, t2l, x2, t2r))
      | T (RED, t2l, x2, t2r) => let
          val+ T (BLK, t2ll, x2l, t2lr) = t2l
          val [c_new:int] t_new = balinc_r (t2lr, x2, rbtree_clr_trans_blk_red t2r)
        in
          T {..}{..}{..}{c_new} (RED, T (BLK, t1, x, t2ll), x2l, t_new)
        end // end of [T (RED, ...)]
    end // end of [_]
end // end of [balrem_l]

fn{elt:t@ype} balrem_r
  {c1,c2:clr} {bh:nat} {v:nat} (
    t1: rbtree0 (elt, c1, bh+1)
  , x: elt
  , t2: rbtree (elt, c2, bh, v)
  ) :<> [c:clr;v:nat | v <= c1] rbtree (elt, c, bh+1, v) = let
(*
** // nothing
*)
in
  case+ t2 of
  | T (RED, t2l, x2, t2r) =>
      T {..}{..}{..}{c1} (RED, t1, x, T (BLK, t2l, x2, t2r))
    // end of [T (RED, ...)]
  | _ =>> begin case+ t1 of
      | T {..} {c1,c1l,c1r} (BLK, t1l, x1, t1r) =>
          balinc_l (T {..}{..}{..}{c1l+c1r} (RED, t1l, x1, t1r), x, t2)
      | T (RED, t1l, x1, t1r) => let
          val+ T (BLK, t1rl, x1r, t1rr) = t1r
          val [c_new:int] t_new = balinc_l (rbtree_clr_trans_blk_red t1l, x1, t1rl)
        in
          T {..}{..}{..}{c_new} (RED, t_new, x1r, T (BLK, t1rr, x, t2))
        end // end of [T (RED, ...)]
    end // end of [_]
end // end of [balrem_r]

(* ****** ****** *)

fun{elt:t@ype} rbtree_remove_min
  {c:clr} {bh:nat | bh+c > 0} .<bh,c>. (
    t: rbtree0 (elt, c, bh), rx: &elt? >> elt, bhdf: &int? >> int (bhdf)
  ) :<> #[bhdf:two | bhdf <= bh]
    [c1:clr | c1 <= c+bhdf] rbtree (elt, c1, bh-bhdf, 0) = let
(*
** // nothing
*)
in
  case+ t of
  | T (BLK, t1, x, t2) => begin case+ t1 of
    | T _ => let
        val t1 = rbtree_remove_min (t1, rx, bhdf) in
        if bhdf = 0 then
          T {..}{..}{..}{0} (BLK, t1, x, t2)
        else let
          val t = balrem_l (t1, x, t2)
        in
          case+ t of
          | T (RED, t1, x, t2) => (bhdf := 0; T (BLK, t1, x, t2)) | _ =>> t
        end (* end of [if] *)
      end // end of [T]
    | E _ => (rx := x; bhdf := 1; t2)
    end (* end of [T (BLK, ...)] *) 
  | T (RED, t1, x, t2) => begin case+ t1 of
    | T _ => let
        val t1 = rbtree_remove_min (t1, rx, bhdf)
      in
        if bhdf = 0 then
          T {..}{..}{..}{0} (RED, t1, x, t2)
        else begin // bhdf = 1
          bhdf := 0; balinc_r (t1, x, rbtree_clr_trans_blk_red t2)
        end (* end of [if] *)
      end // end of [T (BLK, ...)]
    | E () => (rx := x; bhdf := 0; t2)
    end (* end of [T (RED, ...)] *)
end // end of [rbtree_remove_min]

(* ****** ****** *)

fn{elt:t@ype} rbtree_join {c1,c2:clr} {bh:nat} (
    t1: rbtree0 (elt, c1, bh), t2: rbtree0 (elt, c2, bh)
  ) :<> [c:clr;v:nat | v <= c1+c2] rbtree (elt, c, bh, v) =
  case+ t2 of
  | T _ => let
      var rx: elt and bhdf: int // uninmitialized
      val [c2:int] t2 = rbtree_remove_min (t2, rx, bhdf)
    in
      if bhdf = 0 then T {..}{..}{..}{c1+c2} (1(*red*), t1, rx, t2) else balrem_r (t1, rx, t2)
    end // end of [T]
  | E () => t1
// end of [rbtree_join]

(* ****** ****** *)

extern fun{elt:t@ype} rbtree_remove
  {c:clr} {bh:nat} ( // tag = 0/1 : not removed / removed
    t: rbtree0 (elt, c, bh), x0: elt, tag: &int? >> int, cmp: cmp elt
  ) :<> [c1:clr;bh1:nat] rbtree0 (elt, c1, bh1)

implement{elt} rbtree_remove (t, x0, tag, cmp) = let
  fun rem {c:clr} {bh:nat} .<bh,c>.
    (t: rbtree0 (elt, c, bh), tag: &int? >> int, bhdf: &int? >> int bhdf)
    :<cloref> #[bhdf:two | bhdf <= bh] [c1:clr | c1 <= c+bhdf] rbtree0 (elt, c1, bh-bhdf) =
    case+ t of
    | T (BLK, t1, x, t2) => let
        val sgn = compare_elt_elt (x0, x, cmp)
      in
        if sgn < 0 then let
          val t1 = rem (t1, tag, bhdf)
        in
          if bhdf = 0 then
            T {..}{..}{..}{0} (BLK, t1, x, t2)
          else let // bhdf = 1
            val t = balrem_l (t1, x, t2) in case+ t of
            | T (RED, t1, x, t2) => (bhdf := 0; T (BLK, t1, x, t2)) | _ =>> t
          end // end of [if]
        end else if sgn > 0 then let
          val t2 = rem (t2, tag, bhdf)
        in
          if bhdf = 0 then
            T {..}{..}{..}{0} (BLK, t1, x, t2)
          else let // bhdf = 1
            val t = balrem_r (t1, x, t2) in case+ t of
            | T (RED, t1, x, t2) => (bhdf := 0; T (BLK, t1, x, t2)) | _ =>> t
          end // end of [if]
        end else let // x0 = x
          val () = tag := 1 // ; val () = rx := x
          val t = rbtree_join (t1, t2)
        in
          case+ t of
          | T (RED, t1, x, t2) => (bhdf := 0; T (BLK, t1, x, t2)) | _ =>> (bhdf := 1; t)
        end (* end of [if] *)
      end // end of [T (BLK, ...)]
    | T (RED, t1, x, t2) => let
        val sgn = compare_elt_elt (x0, x, cmp)
      in
        if sgn < 0 then let
          val t1 = rem (t1, tag, bhdf)
        in
          if bhdf = 0 then
            T {..}{..}{..}{0} (RED, t1, x, t2)
          else let // bhdf = 1
             val () = bhdf := 0 in balrem_l (t1, x, t2)
          end // end of [if]
        end else if sgn > 0 then let
          val t2 = rem (t2, tag, bhdf)
        in
          if bhdf = 0 then
            T {..}{..}{..}{0} (RED, t1, x, t2)
          else let // bhdf = 1
             val () = bhdf := 0 in balrem_r (t1, x, t2)
          end // end of [if]
        end else let // x0 = x
          val () = tag := 1 // ; val () = rx := x
        in
          bhdf := 0; rbtree_join (t1, t2)
        end (* end of [if] *)
      end // end of [T (RED, ...)]
    | E () => (tag := 0; bhdf := 0; t)
  // end of [rem]
  var bhdf: int // uninitialized
in
  rem (t, tag, bhdf)
end // end of [rbtree_remove]

(* ****** ****** *)

(* end of [funrbtree.dats] *)
