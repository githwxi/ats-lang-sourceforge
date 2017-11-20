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

abstype funarray_t (a:t@ype+ (*element*),  n:int (*size*))

typedef farr (a: t@ype, n: int) = funarray_t (a, n) // an abbreviation

(* ****** ****** *)

fun funarray_nil {a:t@ype} (): farr (a, 0) // not a template!

(* ****** ****** *)

// compute the size of [A]
fun{a:t@ype} funarray_length (* O(log^2(n)) *)
  {n:nat} (A: farr (a, n)):<(*pure*)> int n

(* ****** ****** *)

// obtain the element stored in 'A[i]'
fun{a:t@ype} funarray_get_elt_at (* O(log(n)) *)
  {n:nat} (A: farr (a, n), i: natLt n):<(*pure*)> a

// update 'A[i]' with 'x'; note that this creates a new array!
fun{a:t@ype} funarray_set_elt_at (* O(log(n)) *)
  {n:nat} (A: farr (a, n), i: natLt n, x: a):<(*pure*)> farr (a, n)

overload [] with funarray_get_elt_at
overload [] with funarray_set_elt_at
  
(* ****** ****** *)

// exchange elements stored in 'A[i]' and 'x'
fun{a:t@ype} funarray_xch_elt_at (* O(log(n)) *)
  {n:nat} (A: farr (a, n), i: natLt n, x: &a >> a):<(*pure*)> farr (a, n)

(* ****** ****** *)

// insert an element to the start of the array
fun{a:t@ype} funarray_loadd (* O(log(n)) *)
  {n:nat} (A: farr (a, n), x: a):<(*pure*)> farr (a, n+1)

// remove an element from the start of the array
fun{a:t@ype} funarray_lorem (* O(log(n)) *)
  {n:pos} (A: farr (a, n)):<(*pure*)> farr (a, n-1)

// remove an element from the start of the array and obtain it
fun{a:t@ype} funarray_lorem_get (* O(log(n)) *)
  {n:pos} (A: farr (a, n), x: &a? >> a):<(*pure*)> farr (a, n-1)

(* ****** ****** *)

// insert an element to the end of the array
fun{a:t@ype} funarray_hiadd (* O(log(n)) *)
  {n:nat} (A: farr (a, n), n: int n, x: a):<(*pure*)> farr (a, n+1)

// remove an element from the end of the array
fun{a:t@ype} funarray_hirem (* O(log(n)) *)
  {n:pos} (A: farr (a, n), n: int n):<(*pure*)> farr (a, n-1)

// remove an element from the end of the array and obtain it
fun{a:t@ype} funarray_hirem_get (* O(log(n)) *)
  {n:pos} (A: farr (a, n), n: int n, x: &a? >> a):<(*pure*)> farr (a, n-1)

(* ****** ****** *)

(*
** these higher-order functions are probably not particularly useful as
** they can be readily replaced with for-loops. See the implementation.
*)

fun{a:t@ype} funarray_foreach_cloptr {n:nat} {f:eff}
 (A: farr (a, n), n: int n, f: !a -<cloptr,f> void):<f> void

fun{a:t@ype} funarray_foreach_cloref {n:nat} {f:eff}
 (A: farr (a, n), n: int n, f:  a -<cloref,f> void):<f> void

fun{a:t@ype} funarray_iforeach_cloptr {n:nat} {f:eff}
 (A: farr (a, n), n: int n, f: !(natLt n, a) -<cloptr,f> void):<f> void

fun{a:t@ype} funarray_iforeach_cloref {n:nat} {f:eff}
 (A: farr (a, n), n: int n, f:  (natLt n, a) -<cloref,f> void):<f> void

(* ****** ****** *)

(* end of [funarray.sats] *)
