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

absviewtype linstacklst_vt
  (a:viewt@ype (*element*), n:int (*size*))
stadef stack = linstacklst_vt // an abbreviation

(* ****** ****** *)

// always inline
fun{} linstacklst_nil {a:viewt@ype} ():<> stack (a, 0)

(* ****** ****** *)

// always inline
fun{} linstacklst_is_nil {a:viewt@ype}
  {n:nat} (xs: !stack (a, n)):<> bool (n==0)

// always inline
fun{} linstacklst_is_cons {a:viewt@ype}
  {n:nat} (xs: !stack (a, n)):<> bool (n > 0)

(* ****** ****** *)

fun{a:viewt@ype} linstacklst_push {n:nat} // O(1)
  (xs: &stack (a, n) >> stack (a, n+1), x: a):<> void

fun{a:viewt@ype} linstacklst_pop {n:pos} // O(1)
  (xs: &stack (a, n) >> stack (a, n-1)):<> a

(*
** only allowed for a stack storing nonlinear elements.
*)
fun{a:t@ype} linstacklst_top {n:pos} (xs: &stack (a, n)):<> a

(* ****** ****** *)

fun{a:viewt@ype} linstacklst_size {n:nat} (xs: !stack (a, n)):<> int n

(* ****** ****** *)

fun{a:viewt@ype}
  linstacklst_foreach_cloptr {n:nat} {f:eff}
  (xs: !stack (a, n), f: !(&a) -<cloptr,f> void):<f> void

(* ****** ****** *)

(* end of [linstacklst.sats] *)
