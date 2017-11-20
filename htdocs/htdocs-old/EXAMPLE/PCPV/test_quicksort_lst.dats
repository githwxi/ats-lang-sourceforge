(*
** Some simple testing code
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "libats/DATS/gflist.dats"

(* ****** ****** *)

#include "quicksort_lst.dats"

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

typedef T = double

(* ****** ****** *)

fun listgen {n:nat} .<n>.
  (n: int n): list_vt (T, n) = let
  fun loop {n:nat}
    (n: int n, res: &List_vt(T)? >> list_vt (T, n)): void =
  if n > 0 then let
    val x = drand48 ()
    val () = res := list_vt_cons {T} {0} (x, ?)
    val+ list_vt_cons (_, !p_res) = res
    val () = loop (n-1, !p_res)
    prval () = fold@ (res)
  in
    // nothing
  end else (res := list_vt_nil)
  var res: List_vt(T)?
  val () = loop (n, res)
in
  res
end // end of [listgen]

fn listgen {n:nat}
  (n: int n): list (T, n) = let
  val xs = listgen (n) in list_of_list_vt (xs)
end // end of [listgen]

fun print_list (xs: List (T), i: int): void =
  case+ xs of
  | list_cons (x, xs) => (
      if i > 0 then print ", "; print x; print_list (xs, i+1)
    ) // end of [list_cons]
  | list_nil () => ()
// end of [print_list]

(* ****** ****** *)

implement
main () = () where {
//
  val () = srand48_with_time ()
//
  #define N 10
(*
  #define N 1000000
*)
//
  val xs = listgen (N)
  val () = (print_list (xs, 0); print_newline ())
  val (_pf | xs) = gflist_of_list {T} (xs)
  extern fun lte {x1,x2:int} (
    x1: elt (T, x1), x2: elt (T, x2)
  ) : bool (x1 <= x2) = "atspre_lte_double_double"
  val (_pf | ys) = qsrt<T> (xs, lte)
  val (_pf | ys) = list_of_gflist {T} (ys)
  val () = (print_list (ys, 0); print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [test_quicksort_lst.dats] *)
