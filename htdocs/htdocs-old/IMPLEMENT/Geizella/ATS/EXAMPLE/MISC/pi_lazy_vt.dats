//
//
// using Euler's transform to compute the constant pi 
//
// author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//
//

(* ****** ****** *)

staload "prelude/DATS/lazy.dats"

(* ****** ****** *)

stadef stream = stream_vt
stadef strcon = stream_vt_con

#define nil stream_vt_nil
#define cons stream_vt_cons
#define :: stream_vt_cons

(* ****** ****** *)

// pi/4 = 1/1 - 1/3 + 1/5 - 1/7 + ...

fun pi_stream_con
  (c: double, sum: double, n: Pos): strcon double =
  sum :: pi_stream (~c, sum + (c / double_of n), n+2)

and pi_stream (c: double, sum: double, n: Pos): stream double =
  $delay (pi_stream_con (c, sum, n))

fun euler_trans_con (xs0: stream double): strcon double =
  let
     val- ~(x0 :: !xs1) = lazy_force<strcon double> xs0
     val- xs1_con as x1 :: !xs2 = lazy_vt_force<strcon double> !xs1
     val- xs2_con as x2 :: !xs3 = lazy_vt_force<strcon double> !xs2
     val () = (fold@ xs2_con; !xs2 := $delay_vt xs2_con)
     val () = (fold@ xs1_con; !xs1 := $delay_vt xs1_con)
     val x01 = x0 - x1 and x21 = x2 - x1
  in
     (x2 - x21 * x21 / (x21 + x01)) :: euler_trans xs1
  end

and euler_trans (xs0: stream double): stream double =
  $delay (euler_trans_con xs0)

(* ****** ****** *)

extern fun lazy_vt_destroy {a:viewt@ype} (lazy_vt a): void

fun{a:viewt@ype}
  stream_vt_nth (xs: stream a, i: Nat): a = begin
  case+ lazy_vt_force<strcon a> xs of
  | ~(x :: xs) => begin
      if i = 0 then (lazy_vt_destroy xs; x) else stream (i-1, xs)
    end
  | ~nil () => $raise StreamSubscriptException ()
end // end of [stream_vt_nth]

fun pi_compute {n:nat} (n: int n): double = let
  fun loop {i:nat| i <= n}
    (n: int n, i: int i, xs: stream double): double =
    if i < n then loop (n, i+1, euler_trans xs) else stream_nth (xs, 0)
in
  loop (n, 0, pi_stream (4.0, 0.0, 1))
end // end of [pi_compute]

(* ****** ****** *)

implement main (argc, argv) = let

val pi = pi_compute (8) // pi_compute (10) gives nan

in

printf ("pi = %.13f\n", @(pi)) ;

end

(* ****** ****** *)

(* end of [pi_lazy.dats] *)
