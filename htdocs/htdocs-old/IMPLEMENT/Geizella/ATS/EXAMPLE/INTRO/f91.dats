//
//
// An implementation of the MacCarthy's 91-function
//
// Hongwei Xi (Summer 2007)
//

//
// How to compile:
//
// atscc -o f91 f91.dats
//

// [f91] is proven to be terminating
fun f91 {i:int} .<max(101-i,0)>. (N: int i)
  :<> [j:int | (i <= 100 && j == 91) || (i > 100 && j == i-10)] int j =
  if N > 100 then N-10 else f91 (f91 (N+11))

fn f91_usage (cmd: string): void =
  prerrf ("Usage: %s [integer]\n", @(cmd)) // print an error message

implement main (argc, argv) = let
  val () = if argc <> 2 then (f91_usage (argv.[0]); exit (1))
  val () = assert (argc = 2)
  val s = argv.[1]
  val i = int1_of s
  val res = f91 i
in
   printf ("f91(%i) = %i\n", @(i, res))
end // end of [main]

(* ****** ****** *)

(* end of [f91.dats] *)
