//
// The code was originally written by Hongwei Xi in the Summer of 2004
// It is one of the first programs implemented in ATS.
//

staload "libc/SATS/stdlib.sats"
staload "libc/SATS/time.sats"
staload "libc/SATS/unistd.sats"

// Implementing the eight-queen problem

val clear = "[H[2J" // clear the screen
val home = "[H" // moving the the home position (upper left corner )
val cuu = "[1A" // moving up
val cud = "[1B" // moving down

#define PAUSE 0x1000

fun repeat {n:nat} .<n>. (n: int n, f: () -> void): void =
  if n > 0 then (f (); repeat (n-1, f)) else ()

fun pause (npause: Nat): void = let
  fun loop (n: int): void =
    if n > 0 then (usleep (PAUSE); loop (n-1))
in
  loop (1 << npause)
end // end of [pause]

fun print_spaces (n: Int): void =
  if n igt 0 then repeat (n, lam () => print "  ")

fun print_dots (n: Int): void = // print n dots
  if n igt 0 then repeat (n, lam () => print " .")

fun print_board {s:nat} {l:addr}
  (pf: !array_v (Nat, s, l) | board: ptr l, len: int s)
  : void = let
  fun aux {i:nat | i <= s} .<s-i>.
    (pf: !array_v (Nat, s, l) | i: int i):<cloptr1> void =
    if i < len then let
      val (qi: Nat) = board[i]
    in
      if qi igt 0 then begin
        print_dots (qi - 1); print " Q"; print_dots (len - qi);
        print_newline ();
        aux (pf | i + 1)
      end else begin
        print_dots len; print_newline (); aux (pf | i + 1)
      end
    end
  else begin
    print_newline ()
  end
in
  aux (pf | 0)
end // end of [print_board]

//

fun board_make {sz:nat} (sz: int sz)
  : [l:addr] (free_gc_v l, array_v (Nat, sz, l) | ptr l) = let

val (pf_ngc, pf | p) = array_ptr_alloc_tsz {Nat} (sz, sizeof<Nat>)
fn f (x: &Nat? >> Nat, i: natLt sz):<cloptr> void = x := 0
val () = begin
  array_ptr_initialize_fun_tsz_cloptr {Nat} (| !p, sz, f, sizeof<Nat>)
end

in

(pf_ngc, pf | p)

end

%{^

#include "prelude/CATS/array.cats"
#include "libc/CATS/stdlib.cats"
#include "libc/CATS/time.cats"
#include "libc/CATS/unistd.cats"

%}

fun play {sz:int | sz > 0}
  (npause: Nat, len: int sz): void = let
  var nsol: Nat = 0
  val [l:addr] (pf_ngc, pf_board | board) = board_make (len)

  fun test {i,j:nat | j <= i && i < sz}
    (pf1: !array_v (Nat, sz, l) | j: int j, i: int i, qi: Nat)
    :<cloptr1> Bool =
    if j < i then let
      val (qj: Nat) = board[j]
    in
      if qi = qj then false
      else if iabs (qi - qj) = (i - j) then false
      else test (pf1 | j + 1, i, qi)
    end else begin
      true
    end

  fun loop {i:nat | i < sz}
    (pf1: !array_v (Nat, sz, l), pf2: !Nat @ nsol | i: int i)
    :<cloptr1> void = let
    val next = board[i] + 1
  in
    if next > len then let
      val () = board[i] := 0
    in
      if i = 0 then begin
        repeat (len, lam () => (print_spaces (len); print_newline ()))
      end else begin
        loop (pf1, pf2 | i - 1)
      end
    end else let
      val () = board[i] := next
    in
      if test (pf1 | 0, i, next) then
        if (i + 1 = len) then let
          val () = nsol := nsol + 1
          val () = print_board (pf1 | board, len)
          val () = begin
            print "The solution no. "; print nsol; print " is found!\n";
            print_newline ()
          end 
          val () = pause npause
          val () = print_board (pf1 | board, len)
          val () = repeat (len + 1, lam () => print cuu)
          val () = pause npause
        in
          loop (pf1, pf2 | i)
        end else let
          val () = print_board (pf1 | board, len)
          val () = repeat (len + 1, lam () => print cuu)
          val () = pause npause
        in
          loop (pf1, pf2 | i + 1)
        end // end of [if]
      else begin
        loop (pf1, pf2 | i)
      end // end of [if]
    end // end of [if]
  end // end of [loop]
in
  print (clear);
  loop (pf_board, view@ nsol | 0);
  array_ptr_free {Nat} (pf_ngc, pf_board | board);
  repeat (len, lam () => print cuu)
end // end of [play]

fun usage (): void = begin
  print ("The board size needs to be positive!\n")
end

//

implement main (argc, argv) = let
  var len: Nat = 8
  var npause: Nat = 4
in
  if argc >= 2 then len := max (4, atoi argv.[1]);

  if argc >= 3 then
    let val n = atoi argv.[2] in
       npause := min (max (0, n), 8)
    end;

  let val n = len in
    if n > 0 then
      let
         val start = time ()
         val () = play (npause, n)
         val finish = time ()
         val diff = difftime (finish, start)
      in
         printf ("The amount of time spent on this run is %.0f seconds.", @(diff));
         print_newline ()
      end
    else usage ()
  end // end of [let]
end // end of [main]

(* ****** ****** *)

(* end of [queens.dats] *)
