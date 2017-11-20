//
//
// Some implementations of the Fibonacci function
//
// Hongwei Xi (September, 2007)
//

//
// How to compile:
//
// atscc -o fibs fibs.dats -lgmp
//

fun fib1 (x: int): int =
  if x > 1 then fib1 (x-1) + fib1 (x-2) else x

//

fun fib2 (x: Nat): Nat =
  if x > 1 then fib2 (x-1) + fib2 (x-2) else x

//

fun fib3 (x: Nat): Nat =
  let
    fun loop (x: Nat, a0: Nat, a1: Nat): Nat =
      if x > 0 then loop (x-1, a1, a0 + a1)
      else a0
  in
    loop (x, 0, 1)
  end

//

dataprop FIB (int, int) =
  | FIB_bas_0 (0, 0)
  | FIB_bas_1 (1, 1)
  | {i:nat} {r0,r1:int}
    FIB_ind (i+2, r0+r1) of (FIB (i, r0), FIB (i+1, r1))

fun fib4 {n:nat} (x: int n): [r:int] (FIB (n, r) | int r) =
  let
    fun loop {i,j:nat | i+j == n} {r0,r1:int}
      (pf0: FIB (j, r0), pf1: FIB (j+1, r1) | x: int i, a0: int r0, a1: int r1)
      : [r:int] (FIB (n, r) | int r) =
      if x > 0 then loop (pf1, FIB_ind (pf0, pf1) | x-1, a1, a0 + a1)
      else (pf0 | a0)
  in
    loop (FIB_bas_0 (), FIB_bas_1 () | x, 0, 1)
  end

//

%{^

#include "libc/CATS/gmp.cats"
#include "libats/CATS/intinf.cats"

%}

staload "libats/SATS/intinf.sats"
dynload "libats/DATS/intinf.dats"

fun fib5 {n:nat} (x: int n): [r:int] (FIB (n, r) | intinf r) =
  let
    fun loop {i,j:nat | i+j == n} {r0,r1:int}
      (pf0: FIB (j, r0), pf1: FIB (j+1, r1) |
       x: int i, a0: intinf r0, a1: intinf r1)
      : [r:int] (FIB (n, r) | intinf r) =
      if x > 0 then 
        let val a2 = a0 + a1 in
          intinf_free a0;
          loop (pf1, FIB_ind (pf0, pf1) | x-1, a1, a2)
        end
      else begin
        intinf_free a1; (pf0 | a0)
      end
    val intinf_0 = intinf_of 0 and intinf_1 = intinf_of 1
  in
    loop (FIB_bas_0 (), FIB_bas_1 () | x, intinf_0, intinf_1)
  end

implement main (argc, argv) = let

val () =
  if argc < 2 then begin
    prerrf ("Usage: %s [integer]\n", @(argv.[0]));
    exit 1
  end
val () = assert (argc >= 2)
val n = int1_of (argv.[1])
val () =
  if n < 0 then begin
    prerrf ("The argument = %i is illegal.\n", @(n));
    exit 1
  end
val () = assert (n >= 0)

(*
val fib1_n = fib1 n
val fib2_n = fib2 n
val fib3_n = fib3 n
val (_ | fib4_n) = fib4 n
*)
val (_ | fib5_n) = fib5 n

in
(*
printf ("fib1(%i) = ", @(n)); print fib1_n; print_newline ();

printf ("fib2(%i) = ", @(n)); print fib2_n; print_newline ();

printf ("fib3(%i) = ", @(n)); print fib3_n; print_newline ();

printf ("fib4(%i) = ", @(n)); print fib4_n; print_newline ();
*)
printf ("fib5(%i) = ", @(n)); print fib5_n; print_newline ();
intinf_free fib5_n;

end

(* ****** ****** *)

(* end of [fibs.dats] *)
