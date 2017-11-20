(*

// author: Hongwei Xi (August, 2009)

*)

(* ****** ****** *)

%{^

#include "linbitvec.cats"

%}

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"

(* ****** ****** *)

staload V = "linbitvec.dats"
stadef bitvec_t = $V.bitvec_t

(* ****** ****** *)

fun bitvec_make_rand {n:nat}
  (n: size_t n): [l:addr] (free_gc_v l, bitvec_t n @ l | ptr l) = let
  val (pf_gc, pf_vec | p_vec) = $V.bitvec_make (n)
  val () = loop (!p_vec, n, 0) where {
    fun loop {i:nat | i <= n} .<n-i>.
      (vec: &bitvec_t n, n: size_t n, i: size_t i):<!ref> void =
      if i < n then let
        val b = $Rand.randint (2)
        val () = $V.bitvec_set_at (vec, i, b)
        val () = $effmask_exn (assert (b = $V.bitvec_get_at (vec, i)))
      in
        loop (vec, n, i+1)
      end // end of [if]
    // end of [loop]
  } // end of [val]
in
  (pf_gc, pf_vec | p_vec)
end // end of [bitvec_make_rand]

(* ****** ****** *)

fun print_bitvec {n:nat}
  (v: &bitvec_t n, n: size_t n)
  : void = loop (v, n, 0) where {
  fun loop {i:nat | i <= n} .<n-i>.
    (v: &bitvec_t n, n: size_t n, i: size_t i): void =
    if i < n then let
      val () = if i > 0 then print ","
      val () = print ($V.bitvec_get_at (v, i))
    in
      loop (v, n, i+1)
    end // end of [if]
} // end of [print_bitvec]

(* ****** ****** *)

#define N 41
#define N1 0
#define N2 32

val (pf0_gc, pf0_vec | p0_vec) = bitvec_make_rand (N)
val () = print "vec0 = "
val () = print_bitvec (!p0_vec, N)
val () = print_newline ()

val (pf1_gc, pf1_vec | p1_vec) = $V.bitvec_make (N)
val () = $V.bitvec_copy (!p1_vec, !p0_vec, N)
val () = $V.bitvec_xor (!p1_vec, !p0_vec, N)
val () = print "vec1 = "
val () = print_bitvec (!p1_vec, N)
val () = print_newline ()
val () = assert ($V.bitvec_is_empty (!p1_vec, N))

val () = $V.bitvec_neg (!p1_vec, N)
val () = print "vec1 = "
val () = print_bitvec (!p1_vec, N)
val () = print_newline ()
val () = assert ($V.bitvec_is_full (!p1_vec, N))

val (pf1_gc, pf1_vec | p1_vec) = $V.bitvec_make (N)
val () = $V.bitvec_copy (!p1_vec, !p0_vec, N)
val () = $V.bitvec_neg (!p1_vec, N)
val () = $V.bitvec_and (!p1_vec, !p0_vec, N)
val () = print "vec1 = "
val () = print_bitvec (!p1_vec, N)
val () = print_newline ()
val () = assert ($V.bitvec_is_empty (!p1_vec, N))

val (pf1_gc, pf1_vec | p1_vec) = $V.bitvec_make (N)
val () = $V.bitvec_copy (!p1_vec, !p0_vec, N)
val () = $V.bitvec_neg (!p1_vec, N)
val () = $V.bitvec_or (!p1_vec, !p0_vec, N)
val () = print "vec1 = "
val () = print_bitvec (!p1_vec, N)
val () = print_newline ()
val () = assert ($V.bitvec_is_full (!p1_vec, N))

val (pf2_gc, pf2_vec | p2_vec) = bitvec_make_rand (N)
val () = print "vec2 = "
val () = print_bitvec (!p2_vec, N)
val () = print_newline ()

val (pf01_gc, pf01_vec | p01_vec) = bitvec_make_rand (N)
val () = $V.bitvec_copy (!p01_vec, !p0_vec, N)
val () = print "vec01 = "
val () = print_bitvec (!p01_vec, N)
val () = print_newline ()

val () = $V.bitvec_diff (!p01_vec, !p2_vec, N)

val (pf21_gc, pf21_vec | p21_vec) = bitvec_make_rand (N)
val () = $V.bitvec_copy (!p21_vec, !p2_vec, N)
val () = print "vec21 = "
val () = print_bitvec (!p21_vec, N)
val () = print_newline ()

val () = $V.bitvec_diff (!p21_vec, !p0_vec, N)

val () = $V.bitvec_or (!p21_vec, !p01_vec, N)

val () = $V.bitvec_xor (!p0_vec, !p2_vec, N)
val () = assert ($V.bitvec_equal (!p0_vec, !p21_vec, N))

(* ****** ****** *)

implement main () = ()

(* ****** ****** *)

(* end of [test.dats] *)
