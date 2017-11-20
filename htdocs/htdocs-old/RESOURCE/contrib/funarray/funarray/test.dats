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

// How to compile:
//   atscc -o test test.dats funarray.sats funarray.dats

(* ****** ****** *)

staload "funarray.sats"
staload _(*template code*) = "funarray.dats"

(* ****** ****** *)

dynload "funarray.dats"

(* ****** ****** *)

implement main (argc, argv) = let
  typedef farrstr (n:int) = farr (String, n)
(*
  fn prarr {n:nat} (A: farrstr n, n: int n): void = let
    var i: Nat
  in
    for (i := 0; i < n; i := i+1) begin
      printf ("%i\t |->\t %s\n", @(i, A[i]))
    end
  end // end of [prarr]
*)
  fn prarr {n:nat} (A: farrstr n, n: int n): void = begin
    funarray_iforeach_cloref (A, n,
      lam (i, x) =<cloref1> printf ("%i\t |->\t %s\n", @(i, x))
    )
  end // end of [prarr]

  val A = funarray_nil {String} ()
  val A = loop (argc, argv, 0, A) where {
    fun loop {n,i:nat | i <= n}
      (n: int n, ss: &(@[String][n]), i: int i, A: farrstr i)
      : farrstr n = begin
      if i < n then
        loop (n, ss, i+1, funarray_hiadd (A, i, ss.[i]))
      else A
    end // end of [loop]
  }
  val () = prarr (A, argc)
  val A = loop<String> (argc, 0, A) where {
    fun{a:t@ype} loop {n,i:nat | i <= n}
      (n: int n, i: int i, A: farr (a, n-i)): farr (a, 0) = begin
      if i < n then begin
        loop (n, i+1, funarray_lorem A)
      end else A
    end // end of [loop]
  }
  val A = loop (argc, argv, 0, A) where {
    fun loop {n,i:nat | i <= n}
      (n: int n, ss: &(@[String][n]), i: int i, A: farrstr i)
      : farrstr n = begin
      if i < n then
        loop (n, ss, i+1, funarray_loadd (A, ss.[i]))
      else A
    end // end of [loop]
  }
  val () = prarr (A, argc)
in
 // empty
end // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
