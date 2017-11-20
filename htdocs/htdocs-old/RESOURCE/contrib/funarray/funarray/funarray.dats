(*
**
** An implementation of functional arrays based on Braun trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt
//

(* ****** ****** *)

staload "funarray.sats"

(* ****** ****** *)

datatype brauntree (a:t@ype+, int) =
  | {n1,n2:nat | n2 <= n1; n1 <= n2+1}
    B (a, n1+n2+1) of (a, brauntree (a, n1), brauntree (a, n2))
  | E (a, 0) of ()

stadef bt = brauntree // an abbreviation

(* ****** ****** *)

assume funarray_t (a: t@ype, n:int) = brauntree (a, n)

(* ****** ****** *)

implement funarray_nil {a} () = E ()

(* ****** ****** *)

implement funarray_length<a> (A) = size (A) where {
  // this algorithm is taken from a paper by Okasaki
  fun diff {nl,nr:nat | nr <= nl && nl <= nr+1} .<nr>. 
    (nr: int nr, t: bt (a, nl)):<> int (nl-nr) = begin case+ t of
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

  fun size {n:nat} .<n>. (t: bt (a, n)):<> int n = begin
    case+ t of
    | B (_, tl, tr) => begin
        let val nr = size tr in 1 + nr + nr + diff (nr, tl) end
      end // end of [B]
    | E () => 0
  end // end of [size]
} // end of [funarray_length]

(* ****** ****** *)

implement funarray_get_elt_at<a> (A, i) = get_at (A, i) where {
  fun get_at {n,i:nat | i < n} .<n>. (t: bt (a, n), i: int i):<> a =
    if i > 0 then let
      val i2 = i / 2
    in
      if i > i2 + i2 then let
        val+ B (_, tl, _) = t in get_at (tl, i2)
      end else let
        val+ B (_, _, tr) = t in get_at (tr, i2-1)
      end // end of [if]
    end else let
      val+ B (x, _, _) = t in x
    end // end of [if]
} // end of [funarray_get_at]

implement funarray_set_elt_at<a>
  (A, i, x0) = set_at (A, i, x0) where {
  fun set_at {n,i:nat | i < n} .<n>.
    (t: bt (a, n), i: int i, x0: a):<> bt (a, n) =
    if i > 0 then let
      val+ B (x, tl, tr) = t; val i2 = i / 2
    in
      if i > i2 + i2 then begin
        B (x, set_at (tl, i2, x0), tr)
      end else begin
        B (x, tl, set_at (tr, i2-1, x0))
      end // end of [if]
    end else let
      val+ B (_, t1, t2) = t in B (x0, t1, t2)
    end // end of [if]
} // end of [funarray_set_at]

(* ****** ****** *)

implement funarray_xch_elt_at<a>
  (A, i, x0) = xch_at (A, i, x0) where {
  fun xch_at {n,i:nat | i < n} .<n>.
    (t: bt (a, n), i: int i, x0: &a >> a):<> bt (a, n) =
    if i > 0 then let
      val+ B (x, tl, tr) = t; val i2 = i / 2
    in
      if i > i2 + i2 then begin
        B (x, xch_at (tl, i2, x0), tr)
      end else begin
        B (x, tl, xch_at (tr, i2-1, x0))
      end // end of [if]
    end else let
      val x0_val = x0; val+ B (x, t1, t2) = t; val () = x0 := x
    in
      B (x0_val, t1, t2)
    end // end of [if]
} // end of [funarray_xch_at]

(* ****** ****** *)

implement funarray_loadd<a>
  (t, x0) = loadd (t, x0) where {
  fun loadd {n:nat} .<n>.
    (t: bt (a, n), x0: a):<> bt (a, n+1) = begin
    case+ t of
    | B (x, tl, tr) => B (x0, loadd (tr, x), tl)
    | E () => B (x0, E (), E ())
  end // end of [loadd]
} // end of [funarray_loadd]

implement funarray_lorem<a> (t) = lorem (t) where {
  fun lorem {n:int | n > 0} .<n>.
    (t: bt (a, n)):<> bt (a, n-1) = let
    val+ B (_, tl, tr) = t
  in
    case+ tl of
    | B (xl, _, _) => B (xl, tr, lorem tl) | E () => E ()
  end // end of [lorem]
} // end of [brauntree_lorem]

implement funarray_lorem_get<a> (t, x) = let
  val+ B (x0, tl, tr) = t; val () = (x := x0)
in
  case+ tl of
  | B (xl, _, _) => B (xl, tr, funarray_lorem<a> tl) | E () => E ()
end // end of [funarray_lorem_get]

(* ****** ****** *)

implement funarray_hiadd<a>
  (t, n, x0) = hiadd (t, n, x0) where {
  fun hiadd {n:nat} .<n>.
    (t: bt (a, n), n: int n, x0: a):<> bt (a, n+1) =
    if n > 0 then let
      val+ B (x, tl, tr) = t; val n2 = n / 2
    in
      if n > n2 + n2 then begin
        B (x, hiadd (tl, n2, x0), tr)
      end else begin
        B (x, tl, hiadd (tr, n2-1, x0))
      end
    end else begin
      B (x0, E (), E ())
    end // end of [if]
} // end of [funarray_hiadd]

implement funarray_hirem<a>
  (t, n) = hirem (t, n) where {
  fun hirem {n:pos} .<n>.
    (t: bt (a, n), n: int n):<> bt (a, n-1) = let
    val+ B (x, tl, tr) = t; val n2 = n / 2
  in
    case+ tl of
    | B _ => begin
        if n > n2 + n2 then begin
          B (x, tl, hirem (tr, n2))
        end else begin
          B (x, hirem (tl, n2), tr)
        end // end of [if]
      end // end of [B]
    | E () => E ()
  end // end of [hirem]
} // end of [funarray_hirem]

implement funarray_hirem_get<a>
  (t, n, x0) = hirem_get (t, n, x0) where {
  fun hirem_get {n:pos} .<n>.
    (t: bt (a, n), n: int n, x0: &a? >> a):<> bt (a, n-1) = let
    val+ B (x, tl, tr) = t; val n2 = n / 2
  in
    case+ tl of
    | B _ => begin
        if n > n2 + n2 then begin
          B (x, tl, hirem_get (tr, n2, x0))
        end else begin
          B (x, hirem_get (tl, n2, x0), tr)
        end // end of [if]
      end // end of [B]
    | E () => (x0 := x; E ())
  end
  // end of [hirem_get]
} // end of [funarray_hirem_get]

(* ****** ****** *)

implement funarray_foreach_cloptr<a> {n} {f} (A, n, f) = let
  var i: natLte n
in
  for* {i:nat | i <= n} .<n-i>. // termination metric
    (i: int i) => (i := 0; i < n; i := i+1) f (A[i])
end // end of [funarray_foreach]

implement funarray_foreach_cloref<a> {n} {f} (A, n, f) = let
  var i: natLte n
in
  for* {i:nat | i <= n} .<n-i>. // termination metric
    (i: int i) => (i := 0; i < n; i := i+1) f (A[i])
end // end of [funarray_foreach]

(* ****** ****** *)

implement funarray_iforeach_cloptr<a> {n} {f} (A, n, f) = let
  var i: natLte n
in
  for* {i:nat | i <= n} .<n-i>. // termination metric
    (i: int i) => (i := 0; i < n; i := i+1) f (i, A[i])
end // end of [funarray_foreach]

implement funarray_iforeach_cloref<a> {n} {f} (A, n, f) = let
  var i: natLte n
in
  for* {i:nat | i <= n} .<n-i>. // termination metric
    (i: int i) => (i := 0; i < n; i := i+1) f (i, A[i])
end // end of [funarray_foreach]

(* ****** ****** *)

(* end of [funarray.dats] *)
