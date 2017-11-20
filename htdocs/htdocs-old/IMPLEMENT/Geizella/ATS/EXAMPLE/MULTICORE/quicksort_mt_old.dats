%{^

#include "libats/CATS/thunk.cats"

#include "libc/CATS/pthread.cats"
#include "libc/CATS/pthread_locks.cats"

%}

staload "libc/SATS/pthread.sats"
staload "libc/SATS/pthread_locks.sats"

(* ****** ****** *)

staload "libats/SATS/parallel.sats"
dynload "libats/DATS/parallel.dats"

(* ****** ****** *)

typedef T = double

(* ****** ****** *)

fn partition {n:int | n >= 2} {l: addr}
  (pf: !array_v (T, n, l) | A: ptr l, n: int n): natLt n = let
  val mid = nhalf n
  val mid_v = A->[mid]
  fun iteri {i: nat | i < n}
    (pf: !array_v (T, n, l) | i: int i):<cloptr1> natLt n = let
    val Ai = A->[i]
  in
    if (Ai < mid_v) then
      (if (i + 1 < n ) then iteri (pf | i + 1) else i)
    else i
  end 

  fun iterj {j: nat | j < n}
    (pf: !array_v (T, n, l) | j: int j):<cloptr1> natLt n = let
    val Aj = A->[j]
  in
    if (Aj > mid_v) then 
      (if (j >= 1) then iterj (pf | j - 1) else j)
    else j
  end 
    
  fun loop {i,j: nat | i < n; j < n}
    (pf: !array_v (T, n, l) | i: int i, j: int j)
    :<cloptr1> natLt n = let
    val i' = iteri (pf | i)
    val j' = iterj (pf | j)        
  in
    if i' >= j' then j' else let
      val tmp = A->[i']; val () = (A->[i'] := A->[j']; A->[j'] := tmp)
    in
      loop (pf | i' + 1, j' - 1)
    end
  end
in
  loop (pf | 0, n - 1)
end // end of [partition]

fun quicksort {n:nat} {l:addr} 
  (pf: !array_v (T, n, l) | A: ptr l, n: int n): void = begin
  if (n <= 1) then () else let
    val [i:int] pivot = partition (pf | A, n)
    val (pf_mul | ofs) = pivot imul2 sizeof<T>
    prval @(pf1, pf2) = array_v_split (pf_mul, pf)

    val () = quicksort (pf1 | A, pivot)
    and () = quicksort (pf2 | A + ofs, n - pivot)
  in
    pf := array_v_unsplit (pf_mul, pf1, pf2)
  end
end // end of [quicksort]

#define CUTOFF 128

fun quicksort_mt {n:nat} {l:addr} 
  (pf: !array_v (T, n, l) | A: ptr l, n: int n): void = begin
  if (n > CUTOFF) then let
    val [i:int] pivot = partition (pf | A, n)
    val (pf_mul | ofs) = pivot imul2 sizeof<T>
    prval @(pf1, pf2) = array_v_split (pf_mul, pf)

    val par
      () = quicksort_mt (pf1 | A, pivot)
    and
      () = quicksort_mt (pf2 | A + ofs, n - pivot)
  in
    pf := array_v_unsplit (pf_mul, pf1, pf2)
  end else begin
    quicksort (pf | A, n)
  end
end // end of [quicksort_mt]

//

%{^

#include "libc/CATS/random.cats"
#include "libc/CATS/time.cats"

%}

staload Rand = "libc/SATS/random.sats"
staload Time = "libc/SATS/time.sats"

(* ****** ****** *)

fn array_ptr_print {n:nat} {l:addr}
  (pf_arr: !array_v (T, n, l) | A: ptr l, n: int n): void = let
  fn f (i: natLt n, x: &T):<cloptr1> void = begin
    if i > 0 then print ", "; printf ("%.2f", @(x))
  end
in
  iforeach_array_ptr_tsz_cloptr {T} (f, !A, n, sizeof<T>)
end

(* ****** ****** *)

#define N 100.0

fn random_array_ptr_gen {n:nat} (n: int n):<>
  [l:addr | l <> null] (free_gc_v l, array_v (T, n, l) | ptr l) =
  array_ptr_make_fun_tsz_cloptr {T} (
    n
  , lam (x, i) =<cloptr> x := $effmask_ref ($Rand.drand48 () * N)
  , sizeof<T>
  ) // end of [array_ptr_make_fun_tsz_cloptr]

(* ****** ****** *)

fn usage (cmd: string): void = begin
  prerr ("Usage:\n");
  prerrf ("  single core: %s [integer]\n", @(cmd));
  prerrf ("  multiple core: %s [integer(arg)] [integer(core)]\n", @(cmd));
end

implement main (argc, argv) = begin
  if argc >= 2 then let
    var nthread: int = 0
    val n = int1_of argv.[1] // turning string into integer
    val () = assert (n >= 0)
    val () = if argc >= 3 then (nthread := int_of argv.[2])
    val () = parallel_worker_add_many (nthread-1)
    val () = printf ("There are now [%i] workers.", @(nthread))
    val () = print_newline ()
    val (pf_gc, pf_arr | A) = random_array_ptr_gen (n)
(*
    val () = array_ptr_print (pf_arr | A, n)
    val () = print_newline ()
*)
    val () = quicksort_mt (pf_arr | A, n)
(*
    val () = array_ptr_print (pf_arr | A, n)
    val () = print_newline ()
*)
  in
    array_ptr_free {T} (pf_gc, pf_arr | A)
  end else begin
    usage argv.[0]; exit (1)
  end
end // end of [main]

(* ****** ****** *)

(* end of [quicksort_mt.dats] *)

