//
//
// A simple example for testing
//
//

%{^

#include "libc/CATS/random.cats"

%}

staload Rand = "libc/SATS/random.sats"
datatype floatlst = nil | cons of (double, floatlst)

// staload LIST = "prelude/DATS/list.dats"
// typedef floatlst = List double

(*

#define nil list_nil
#define cons list_cons

*)

#define :: cons

fun length (xs: floatlst): int =
  case+ xs of
    | _ :: xs => 1 + length xs
    | nil () => 0

fun append (xs: floatlst, ys: floatlst): floatlst =
  case+ xs of
    | x :: xs => x :: append (xs, ys)
    | nil () => ys

(*
fun append (xs: floatlst, ys: floatlst): floatlst = list_append<double> (xs, ys)
*)

fun print_floatlst (xs: floatlst): void =
  let
    fn pr (x: double): void = printf ("%.2f", @(x))
    fun aux (x: double, xs: floatlst): void =
      case+ xs of
      | x1 :: xs1 => begin
          pr x; print ", "; aux (x1, xs1)
        end
      | nil () => pr x
  in
     case+ xs of x :: xs => aux (x, xs) | nil () => ()
  end

fn floatlst_gen {n:nat} (n: int n): floatlst =
  let
    fun aux {i:nat} .<i>. (i: int i, xs: floatlst): floatlst =
      if i > 0 then aux (i-1, $Rand.drand48 () :: xs) else xs
  in
    aux (n, nil)
  end

// A naive quicksort implementation

typedef lte_double = (double, double) -<> bool

fun qs (lte: lte_double, xs: floatlst): floatlst =
  case+ xs of // case+ mandates exhaustive pattern matching
    | nil () => nil ()
    | x' :: xs' => part (lte, x', xs', nil (), nil ())

and part (lte: lte_double, x: double, xs: floatlst, l: floatlst, r: floatlst)
  : floatlst =
  case+ xs of // case+ mandates exhaustive pattern matching
    | nil () => append (qs (lte, l), (x :: qs (lte, r)))
    | x' :: xs' =>
      if lte (x', x) then part (lte, x, xs', x' :: l, r)
      else part (lte, x, xs', l, x' :: r)

val () = $Rand.srand48_with_time ()
val xs1 = floatlst_gen (10)
val xs2 = append (xs1, xs1)
val xs3 = append (xs2, xs2)
val xs4 = qs (lam (x1, x2) => x1 <= x2, xs3)

val n1 = length xs1
val n2 = length xs2
val n3 = length xs3
val n4 = length xs4

val () = begin
  print "n1 = "; print n1; print_newline ();
  print_floatlst xs1; print_newline ();
  print "n2 = "; print n2; print_newline ();
  print_floatlst xs2; print_newline ();
  print "n3 = "; print n3; print_newline ();
  print_floatlst xs3; print_newline ();
  print "n4 = "; print n3; print_newline ();
  print_floatlst xs4; print_newline ();
end

//

implement main (argc, argv) = ()

(* end of [floatlst] *)
