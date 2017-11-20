//
//
// Author: Hongwei Xi (August 2007)
//
// This is an example of programming with theorem proving: A verified
// implmentation of the factioral function is given.

//
// How to compile:
//
// atscc -o fact3 fact3.dats -lgmp
//

%{^

#include "libc/CATS/gmp.cats"
#include "libats/CATS/intinf.cats"

%}

staload "libats/SATS/intinf.sats"
dynload "libats/DATS/intinf.dats"

// The following dataprop encodes a specification of the factorial function
dataprop FACT (int, int) =
  | FACTzero (0, 1)
  | {n,r,r1:int | n > 0} FACTsucc (n, r) of (FACT (n-1, r1), MUL (n, r1, r))

fun fact3 {n:nat} .<n>. (n: !intinf n): [r:int] (FACT (n, r) | intinf r) =
  if n > 0 then let
    val n1 = pred n
    val (pf1 | r1) = fact3 (n1)
    val () = intinf_free n1
    val (pf_mul | r) = n * r1
    val () = intinf_free r1
  in
    (FACTsucc (pf1, pf_mul) | r)
  end else begin
    (FACTzero () | intinf_of 1)
  end

// [fn] declares a non-recursive function
// [@(...)] is used in ATS to group arguments for functions of variable arguments
fn fact3_usage (cmd: string): void =
  prerrf ("Usage: %s [integer]\n", @(cmd)) // print an error message

// is there any doubt :)
implement main (argc, argv) =
  if argc >= 2 then let
    val n0 = int1_of argv.[1] // turning string into integer
    val () = assert_errmsg
      (n0 >= 0, "The integer argument needs to be nonnegative.\n")
    val n = intinf_of n0
    val (pf | res) = fact3 (n)
    val () = intinf_free n
  in
    print "The factorial of "; print n0; print " = ";
    print res; print_newline (); intinf_free res
  end else begin
    fact3_usage (argv.[0]); exit (1)
  end

(*

The factorial of 100 =
93326215443944152681699238856266700490715968264381
62146859296389521759999322991560894146397615651828
62536979208272237582511852109168640000000000000000
00000000

*)

(* ****** ****** *)

(* end of [fact3.dats] *)
