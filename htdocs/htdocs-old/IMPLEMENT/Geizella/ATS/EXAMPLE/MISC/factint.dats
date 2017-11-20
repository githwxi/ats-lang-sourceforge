typedef T = int

#define zero 0
#define one  1
fn ofstring_absint (s: string): T = int_of s

#define ABSINT ~1
#include "EXAMPLE/MISC/factabs.dats"

fn fact_usage (cmd: string): void =
  prerrf ("Usage: %s [integer]\n", @(cmd)) // print an error message

implement main (argc, argv) =
  if argc >= 2 then let
    val n = ofstring_absint argv.[1] // turning string into integer
    val res = fact n
  in
    print "factorial of "; print n; print " = "; print res; print_newline ()
  end else begin
    fact_usage argv.[0]; exit (1)
  end

(* ****** ****** *)

(* end of [factint.dats] *)
