(*

// Implementing Erathosthene's sieve in linear-lazy style

// author: Hongwei Xi (February, 2008)

*)

(* ****** ****** *)

staload "prelude/DATS/lazy.dats"
staload "prelude/DATS/reference.dats"

(* ****** ****** *)

#define nil stream_vt_nil
#define :: stream_vt_cons

(* ****** ****** *)

extern fun lazy_vt_destroy {a:viewt@ype} (x: lazy_vt a): void
  = "ats_lazy_vt_destroy"

%{$

ats_void_type ats_lazy_vt_destroy (ats_ptr_type x) { return ; }

%}

fun{a:t@ype}
  stream_vt_nth (xs0: stream_vt a, i: Nat): a = let
(*
  val () = begin
    print "stream_vt_nth: before: i = "; print i; print_newline ()
  end
*)
  val xs0_con = lazy_vt_force xs0
in
  case+ xs0_con of
  | ~(x :: xs) => begin
      if i = 0 then (lazy_vt_destroy xs; x) else stream_vt_nth (xs, i-1)
    end
  | ~nil () => $raise StreamSubscriptException ()
end // end of [stream_vt_nth]

(* ****** ****** *)

fun from_con {n:int} (n: int n): stream_vt_con (intGte n) = n :: from (n+1)
and from {n:int} (n: int n): stream_vt (intGte n) = $delay (from_con n)

//

typedef Nat2 = intGte 2

fun sieve_con (ns: stream_vt Nat2): stream_vt_con (Nat2) =
  let
(*
     val () = begin
       print "sieve_con: enter"; print_newline ()
     end
*)
     val ns_con = lazy_vt_force ns
     val- n :: !ns = ns_con
(*
     val () = begin
       print "sieve_con: n = "; print n; print_newline ()
     end
*)
     val ns_val = !ns
     val () = (!ns := sieve (stream_vt_filter<Nat2> (ns_val, lam x => x nmod n > 0)))
  in
     fold@ ns_con; ns_con
  end

and sieve (ns: stream_vt Nat2): stream_vt (Nat2) = $delay (sieve_con ns)

//

fn primes (): stream_vt Nat2 = sieve (from 2)
fn prime (n: Nat): Nat = stream_vt_nth (primes (), n)

//

implement main (argc, argv) = begin

//printf ("prime 1000 = %i\n", @(prime 1000)) ; // 7927
printf ("prime 10000 = %i\n", @(prime 10000)) ; // 104743
//printf ("prime 20000 = %i\n", @(prime 20000)) ; // 224743
//printf ("prime 30000 = %i\n", @(prime 30000)) ; // = 350381 (2 min.)
//printf ("prime 50000 = %i\n", @(prime 50000)) ; // = 611957 (6 min.)

end

(* ****** ****** *)

(* end of [sieve_lazy_vt.dats] *)
