(*
**
** An implementation of linear stacks based on lists
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

absviewtype linstacklst_vt
  (a:viewt@ype (*element*), n:int (*size*))

stadef stack = linstacklst_vt // an abbreviation

(* ****** ****** *)

// always inline
extern fun{} linstacklst_nil {a:viewt@ype} ():<> stack (a, 0)

(* ****** ****** *)

// always inline
extern fun{} linstacklst_is_nil {a:viewt@ype}
  {n:nat} (xs: !stack (a, n)):<> bool (n==0)

// always inline
extern fun{} linstacklst_is_cons {a:viewt@ype}
  {n:nat} (xs: !stack (a, n)):<> bool (n > 0)

(* ****** ****** *)

extern fun{a:viewt@ype} linstacklst_push {n:nat} // O(1)
  (xs: &stack (a, n) >> stack (a, n+1), x: a):<> void

extern fun{a:viewt@ype} linstacklst_pop {n:pos} // O(1)
  (xs: &stack (a, n) >> stack (a, n-1)):<> a

(* ****** ****** *)

// only allowed for a stack storing nonlinear elements.
extern fun{a:t@ype} linstacklst_top {n:pos} (xs: &stack (a, n)):<> a

(* ****** ****** *)

extern fun{a:viewt@ype} linstacklst_size {n:nat} (xs: !stack (a, n)):<> int n

(* ****** ****** *)

extern fun{a:viewt@ype}
  linstacklst_foreach_clo {v:view} {n:nat}
  (pf: !v | xs: !stack (a, n), f: &(!v | &a) -<clo1> void): void

extern fun{a:viewt@ype}
  linstacklst_foreach_cloref {v:view} {n:nat} {f:eff}
  (pf: !v | xs: !stack (a, n), f: !(!v | &a) -<cloref1> void): void

(* ****** ****** *)

assume linstacklst_vt (a: viewt@ype, n: int) = list_vt (a, n)

(* ****** ****** *)

implement{} linstacklst_nil () = list_vt_nil ()

implement{} linstacklst_is_nil (xs) = begin case+ xs of
  | list_vt_cons _ => (fold@ xs; false) | list_vt_nil _ => (fold@ xs; true)
end // end of [linstacklst_is_nil]

implement{} linstacklst_is_cons (xs) = begin case+ xs of
  | list_vt_cons _ => (fold@ xs; true) | list_vt_nil _ => (fold@ xs; false)
end // end of [linstacklst_is_cons]

(* ****** ****** *)

implement{a} linstacklst_size (xs) = loop (xs, 0) where {
  fun loop {i,j:nat} .<i>.
    (xs: !list_vt (a, i), j: int j):<> int (i+j) =
    case+ xs of
    | list_vt_cons (_, !xs1) => let
        val n = loop (!xs1, j+1) in fold@ xs; n
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ xs; j)
} // end of [linstacklst_size]

(* ****** ****** *)

implement{a} linstacklst_push (xs, x) = begin
  let val () = xs := list_vt_cons (x, xs) in () end
end // end of [linstacklst_push]

implement{a} linstacklst_pop (xs) = let
  val+ ~list_vt_cons (x, xs1) = xs; val () = xs := xs1 in x
end // end of [linstacklst_pop]

implement{a} linstacklst_top (xs) = let
  val+ list_vt_cons (x, _) = xs in fold@ xs; x
end // end of [linstacklst_top]

(* ****** ****** *)

implement{a} linstacklst_foreach_clo {v}
  {n} (pf | xs, f) = loop (pf | xs, f) where {
  fun loop {i:nat} .<i>.
    (pf: !v | xs: !list_vt (a, i), f: &(!v | &a) -<clo1> void): void =
    case+ xs of
    | list_vt_cons (!x, !xs1) => (f (pf | !x); loop (pf | !xs1, f); fold@ xs)
    | list_vt_nil () => fold@ xs
} // end of [linstacklst_foreach_clo]

implement{a}
  linstacklst_foreach_cloref {v} {n} (pf0 | tbl, f) = let
  typedef clo_type = (!v | &a) -<clo1> void
  val (vbox pf_f | p_f) = cloref_get_view_ptr {clo_type} (f)
in
  $effmask_ref (linstacklst_foreach_clo<a> {v} (pf0 | tbl, !p_f))
end // end of [linstacklst_foreach_cloref]

(* ****** ****** *)

(* end of [linstacklst.dats] *)
