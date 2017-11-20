(*
**
** An implementation of functional binary heaps based on Braun trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

abstype funbinheap_t (elt:t@ype+ (*element*),  n:int (*size*))
typedef fbinhp (elt: t@ype, n: int) = funbinheap_t (elt, n) // an abbreviation
typedef fbinhp (elt: t@ype) = [n:nat] funbinheap_t (elt, n) // an abbreviation

(* ****** ****** *)

typedef cmp (elt:t@ype) = (elt, elt) -<cloref> Sgn

extern fun{elt:t@ype}
  compare_elt_elt (x1: elt, x2: elt, cmp: cmp elt):<> Sgn

implement{elt} compare_elt_elt (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

datatype brauntree (a:t@ype+, int) =
  | {n1,n2:nat | n2 <= n1; n1 <= n2+1}
    B (a, n1+n2+1) of (a, brauntree (a, n1), brauntree (a, n2))
  | E (a, 0) of ()
// end of [brauntree]

stadef bt = brauntree // an abbreviation

(* ****** ****** *)

assume funbinheap_t (elt:t@ype, n:int) = brauntree (elt, n)

(* ****** ****** *)

extern fun{} funbinheap_empty {elt:t@ype} (): fbinhp (elt, 0)

implement{} funbinheap_empty () = E ()

(* ****** ****** *)

// [funbinheap_size] is of O(log^2 n) time-complexity
extern fun{elt:t@ype}
  funbinheap_size {n:nat} (t: fbinhp (elt, n)):<> int n
// end of ...

implement{elt} funbinheap_size (t) = size (t) where {
  // this algorithm is taken from a paper by Okasaki
  fun diff {nl,nr:nat | nr <= nl && nl <= nr+1} .<nr>. 
    (nr: int nr, t: bt (elt, nl)):<> int (nl-nr) = begin case+ t of
    | B (_, tl, tr) => begin
        if nr > 0 then let
          val nr2 = nr / 2
        in
          if nr > nr2 + nr2 then diff (nr2, tl) else diff (nr2-1, tr)
        end else begin
          1 // return value
        end // end of [if]
      end // end of [B]
     | E () => 0
  end // end of [diff]

  fun size {n:nat} .<n>. (t: bt (elt, n)):<> int n = begin
    case+ t of
    | B (_, tl, tr) => begin
        let val nr = size tr in 1 + nr + nr + diff (nr, tl) end
      end // end of [B]
    | E () => 0
  end // end of [size]
} // end of [funbinheap_size]

(* ****** ****** *)

extern fun{elt:t@ype} funbinheap_insert
  {n:nat} (t: fbinhp (elt, n), x: elt, cmp: cmp elt):<> fbinhp (elt, n+1)

implement{elt} funbinheap_insert (t, x, cmp) = insert (t, x) where {
  fun insert {n:nat} .<n>.
    (t: fbinhp (elt, n), x: elt):<cloref> fbinhp (elt, n+1) =
    case+ t of
    | E () => B (x, E (), E ())
    | B (x0, t1, t2) => begin
        if compare_elt_elt (x0, x, cmp) >= 0 then
          B (x, insert (t2, x0), t1) else B (x0, insert (t2, x), t1)
      end // end of [B]
  // end of [insert]
} // end of [funbinheap_insert]

(* ****** ****** *)

fun{elt:t@ype} brauntree_leftrem {n:pos} .<n>.
  (t: brauntree (elt, n), x_r: &elt? >> elt):<> brauntree (elt, n-1) = let
  val+ B (x, t1, t2) = t
in
  case+ t1 of
  | B _ => let
      val t1 = brauntree_leftrem (t1, x_r) in B (x, t2, t1)
    end // end of [B]
  | E () => (x_r := x; E ())
end // end of [brauntree_leftrem]

(* ****** ****** *)

fun{elt:t@ype} brauntree_siftdn
  {nl,nr:nat | nr <= nl; nl <= nr+1} .<nl>. (
    x: elt
  , tl: brauntree (elt, nl), tr: brauntree (elt, nr)
  , cmp: cmp elt
  ) :<> brauntree (elt, nl+nr+1) = siftdn (x, tl, tr) where {
  fun siftdn {nl,nr:nat | nr <= nl; nl <= nr+1} .<nl+nr>.
    (x: elt, tl: brauntree (elt, nl), tr: brauntree (elt, nr))
    :<cloref> brauntree (elt, nl+nr+1) = case+ (tl, tr) of
    | (B (xl, tll, tlr), B (xr, trl, trr)) => begin
        if compare_elt_elt (xl, x, cmp) >= 0 then begin // xl >= x
          if compare_elt_elt (xr, x, cmp) >= 0 then B (x, tl, tr)
                                               else B (xr, tl, siftdn (x, trl, trr))
          // end of [if]
        end else begin // xl < x
          if compare_elt_elt (xr, x, cmp) >= 0 then B (xl, siftdn (x, tll, tlr), tr)
          else begin // xr < x
            if compare_elt_elt (xl, xr, cmp) >= 0 then B (xr, tl, siftdn (x, trl, trr))
                                                  else B (xl, siftdn (x, tll, tlr), tr)
            // end of [if]
          end // end of [if]
        end (* end of [if] *)
      end (* end of [B _, B _] *)
    | (_, _) =>> begin case+ tl of
      | B (xl, _, _) =>
          if compare_elt_elt (xl, x, cmp) >= 0 then B (x, tl, E) else B (xl, B (x, E, E), E)
        // end of [B]
      | E () => B (x, E (), E ())
      end // end of [_, _]
  // end of [siftdn]
} // end of [brauntree_siftdn]

(* ****** ****** *)

extern fun{elt:t@ype} funbinheap_delmin
  {n:pos} (t: fbinhp (elt, n), x_r: &elt? >> elt, cmp: cmp elt):<> fbinhp (elt, n-1)
// end of [funbinheap_delim]

implement{elt} funbinheap_delmin
  (t, x_r, cmp) = delmin (t, x_r) where {
  fn delmin {n:pos}
    (t: fbinhp (elt, n), x_r: &elt? >> elt)
    :<cloref> fbinhp (elt, n-1) = let
    val+ B (x, t1, t2) = t; val () = x_r := x in
    case+ t1 of
    | B _ => let
        var x_lrm: elt // uninitialized
        val t1 = brauntree_leftrem<elt> (t1, x_lrm) in
        brauntree_siftdn<elt> (x_lrm, t2, t1, cmp)
      end // end of [B]
    | E () => E ()
  end // end of [demin]
} // end of [funbinheap_delmin]

(* ****** ****** *)

(* end of [funbinheap.dats] *)
