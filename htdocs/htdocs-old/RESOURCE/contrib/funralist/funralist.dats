(*
**
** An implementation of functional random-access list based on
** a nested datatype. Please see Okasaki's book for more details
** on this interesting data structure.
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

typedef P (a1:t@ype) (a2:t@ype) = '(a1, a2)

datatype ralist (a:t@ype+, int) =
  | RAnil (a, 0)
  | {n:nat} RAodd (a, n+n+1) of (a, ralist (P a a, n))
  | {n:pos} RAevn (a, n+n) of ralist (P a a, n)

(* ****** ****** *)

extern fun{a:t@ype} ralist_length {n:nat} (xs: ralist (a, n)):<> int n

extern fun{a:t@ype} ralist_head {n:pos} (xs: ralist (a, n)):<> a

extern fun{a:t@ype} ralist_tail {n:pos} (xs: ralist (a, n)):<> ralist (a, n-1)

extern fun{a:t@ype} ralist_cons {n:nat} (x: a, xs: ralist (a, n)):<> ralist (a, n+1)

extern fun{a:t@ype} ralist_uncons {n:pos}
  (xs: ralist (a, n), x_r: &a? >> a):<> ralist (a, n-1)

extern fun{a:t@ype} ralist_lookup {n:nat} (xs: ralist (a, n), i: natLt n):<> a

extern fun{a:t@ype} ralist_update {n:nat}
  (xs: ralist (a, n), i: natLt n, x: a):<> ralist (a, n)
  
(* ****** ****** *)

extern fun{a:t@ype}
  ralist_foreach_clo {v:view} {n:nat} {f:eff}
  (pf: !v | xs: ralist (a, n), f: &(!v | a) -<clo,f> void):<f> void

extern fun{a:t@ype}
  ralist_foreach_cloref {v:view} {n:nat} {f:eff}
  (pf: !v | xs: ralist (a, n), f: !(!v | a) -<cloref,f> void):<f> void

(* ****** ****** *)

macdef P x1 x2 = '(,(x1), ,(x2))

(* ****** ****** *)

implement{a} ralist_length (xs) = length (xs) where {
  fun length {n:nat} .<n>. (xs: ralist (a, n)):<> int n = case+ xs of
    | RAnil _ => 0
    | RAodd (_, ys) => 2 * ralist_length (ys) + 1
    | RAevn xs => 2 * ralist_length (xs)
} // end of [ralist_length]

(* ****** ****** *)

implement{a} ralist_cons (x0, xs) = cons (x0, xs) where {
  fun cons {n:nat} .<n>. (x0: a, xs: ralist (a, n)):<> ralist (a, n+1) =
    case+ xs of
    | RAnil _ => RAodd (x0, RAnil ())
    | RAodd (x, xxs) => RAevn (ralist_cons (P x0 x, xxs))
    | RAevn xxs => RAodd (x0, xxs)
} // end of [ralist_cons]

(* ****** ****** *)

implement{a} ralist_head (xs) = head (xs) where {
  fun head {n:pos} .<n>. (xs: ralist (a, n)):<> a = case+ xs of
    | RAodd (x, _) => x
    | RAevn xxs => begin
        let val xx = ralist_head<P a a> xxs in xx.0 end
      end
} // end of [ralist_head]

(* ****** ****** *)

implement{a} ralist_uncons (xs, x_r) = uncons (xs, x_r) where {
  fun uncons {n:pos} .<n>.
    (xs: ralist (a, n), x_r: &a? >> a):<> ralist (a, n-1) =
    case+ xs of
    | RAodd (x, xxs) => begin
        x_r := x; case+ xxs of RAnil () => RAnil () | _ =>> RAevn xxs
      end // end of [RAodd]
    | RAevn xxs => let
        var xx_r: P a a // uninitialized
        val xxs = ralist_uncons<P a a> (xxs, xx_r)
      in
        x_r := xx_r.0; RAodd (xx_r.1, xxs)
      end // end of [RAevn]
} // end of [ralist_uncons]

(* ****** ****** *)

implement{a} ralist_tail (xs) = tail (xs) where {
  fun tail {n:pos} .<n>. (xs: ralist (a, n)):<> ralist (a, n-1) = case+ xs of
    | RAodd (_, xxs) => begin
        case+ xxs of RAnil () => RAnil () | _ =>> RAevn xxs
      end // end of [RAodd]
    | RAevn xxs => let
        var xx: P a a
        val xxs = ralist_uncons<P a a> (xxs, xx)
      in
        RAodd (xx.1, xxs)
      end // end of [RAevn]
} // end of [ralist_tail]

(* ****** ****** *)

implement{a} ralist_lookup (xs, i) = lookup<a> (xs, i) where {
  fun{a:t@ype} lookup {n,i:nat | i < n} .<n>. (xs: ralist (a, n), i: int i):<> a =
    case+ xs of
    | RAodd (x, xxs) => begin
        if i = 0 then x else let
          val x01 = lookup<P a a> (xxs, nhalf (i-1))
        in
          if i nmod 2 = 0 then x01.1 else x01.0
        end // end of [if]
      end // end of [RAodd]
    | RAevn xxs => let
        val x01 = lookup<P a a> (xxs, nhalf i)
      in
        if i nmod 2 = 0 then x01.0 else x01.1
      end // end of [RAevn]
} // end of [ralist_lookup]

(* ****** ****** *)

// Here is an example of constructing linear closures explicitly

dataviewtype closure_ (a:t@ype) =
  {param: viewtype} CLOSURE_ (a) of (param, (param, a) -<fun> a)

fn{a:t@ype} cloapp (c: closure_ a, x: a):<> a = let
  val+ ~CLOSURE_ {..} {param} (p, f) = c; val f = f: (param, a) -<fun> a
in
  f (p, x)
end // end of [cloapp]
  
fun{a:t@ype} fupdate {n,i:nat | i < n} .<n>.
  (xs: ralist (a, n), i: int i, c: closure_ a):<> ralist (a, n) = let
  fn f0 (c: closure_ a, xx: P a a):<> P a a = '(cloapp<a> (c, xx.0), xx.1)
  fn f1 (c: closure_ a, xx: P a a):<> P a a = '(xx.0, cloapp<a> (c, xx.1))
in
  case+ xs of
  | RAodd (x, xxs) => begin
      if i = 0 then RAodd (cloapp<a> (c, x), xxs) else let
        val i1 = i - 1; val i2 = i1 / 2; val parity = i1 - (i2 + i2)
      in
        if parity = 0 then begin
          RAodd (x, fupdate<P a a> (xxs, i2, CLOSURE_ {P a a} (c, f0)))
        end else begin
          RAodd (x, fupdate<P a a> (xxs, i2, CLOSURE_ {P a a} (c, f1)))
        end // end of [if]
      end // end of [if]
    end // end of [RAodd]
  | RAevn xxs => let
      val i2 = i / 2; val parity = i - (i2 + i2)
    in
      if parity = 0 then begin
        RAevn (fupdate<P a a> (xxs, i2, CLOSURE_ {P a a} (c, f0)))
      end else begin
        RAevn (fupdate<P a a> (xxs, i2, CLOSURE_ {P a a} (c, f1)))
      end // end of [if]
    end // end of [RAevn]
end // end of [fupdate]

implement{a} ralist_update (xs, i, x) = let
  val f0 = lam (x_box: box_vt a, _: a): a =<fun> let val+ ~box_vt (x) = x_box in x end
in
  fupdate<a> (xs, i, CLOSURE_ (box_vt x, f0))
end // end of [ralist_update]

(* ****** ****** *)

implement{a}
  ralist_foreach_clo {v} {n} {f} (pf0 | xs, f) = let
  typedef clo_type = (!v | a) -<clo,f> void
  typedef cloref_type = (!v | a) -<cloref,f> void
  val f = cloref_make_cloptr (view@ f | &f) where {
    extern castfn cloref_make_cloptr {l:addr}
      (pf: !clo_type @ l | p: ptr l):<> cloref_type
  } // end of [where]
  val () = ralist_foreach_cloref<a> {v} (pf0 | xs, f)
in
  // empty
end // end of [ralist_foreach_clo]

fun{a:t@ype} foreach {v:view} {n:pos} {f:eff} .<n>.
  (pf0: !v | xs: ralist (a, n), f: !(!v | a) -<cloref,f> void):<f> void = case+ xs of
  | RAodd (x, xxs) => let
      val () = f (pf0 | x) in case+ xxs of
      | RAnil () => () | _ =>> let
          var !p_f2 with pf_f2 =
            @lam (pf0: !v | xx: P a a): void =<clo,f> (f (pf0 | xx.0); f (pf0 | xx.1))
          typedef clo_type = (!v | P a a) -<clo,f> void
          typedef cloref_type = (!v | P a a) -<cloref,f> void
          val f2 = cloref_make_clo (pf_f2 | p_f2) where { // cutting a corner here!
            extern castfn cloref_make_clo (pf: !clo_type @ p_f2 | p: ptr p_f2):<> cloref_type
          } // end of [val]
        in
          foreach<P a a> (pf0 | xxs, f2)
        end // end of [_]
    end // end of [RAodd]
  | RAevn xxs => let
      var !p_f2 with pf_f2 =
        @lam (pf0: !v | xx: P a a): void =<clo,f> (f (pf0 | xx.0); f (pf0 | xx.1))
      typedef clo_type = (!v | P a a) -<clo,f> void
      typedef cloref_type = (!v | P a a) -<cloref,f> void
      val f2 = cloref_make_clo (pf_f2 | p_f2) where { // cutting a corner here!
        extern castfn cloref_make_clo (pf: !clo_type @ p_f2 | p: ptr p_f2):<> cloref_type
      } // end of [val]
    in
      foreach<P a a> (pf0 | xxs, f2)
    end // end of [RAevn]
// end of [foreach]

implement{a} ralist_foreach_cloref (pf0 | xs, f) = begin
  case+ xs of RAnil () => () | _ =>> foreach<a> (pf0 | xs, f)
end // end of [ralist_foreach_cloref]

(* ****** ****** *)

(* end of [funralist.dats] *)
