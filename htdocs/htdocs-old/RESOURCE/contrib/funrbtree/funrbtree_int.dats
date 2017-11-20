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

staload "funrbtree.dats"
dynload "funrbtree.dats"

(* ****** ****** *)

#define cmp compare_int_int

implement compare_elt_elt<int> (x1, x2, _) = cmp (x1, x2)

val xs = rbtree_nil<> {int} ()
val xs = rbtree_insert<int> (xs, 4, cmp)
val xs = rbtree_insert<int> (xs, 3, cmp)
val xs = rbtree_insert<int> (xs, 2, cmp)
val xs = rbtree_insert<int> (xs, 1, cmp)
val () = (print "size(xs) = "; print (rbtree_size xs); print_newline ())

(* ****** ****** *)

#define cmp compare_double_double

implement compare_elt_elt<double> (x1, x2, _) = cmp (x1, x2)

val xs = rbtree_nil {double} ()
val xs = rbtree_insert<double> (xs, 1.0, cmp)
val xs = rbtree_insert<double> (xs, 2.0, cmp)
val xs = rbtree_insert<double> (xs, 3.0, cmp)
val xs = rbtree_insert<double> (xs, 4.0, cmp)
val () = (print "size(xs) = "; print (rbtree_size xs); print_newline ())

(* ****** ****** *)

implement main () = ()

(* ****** ****** *)

(* end of [funrbtree_int.dats] *)
