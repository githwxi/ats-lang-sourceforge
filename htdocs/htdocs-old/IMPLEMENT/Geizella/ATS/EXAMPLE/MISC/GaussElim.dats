(*
 *
 * An implementation of the Gaussian elimination algorithm in ATS
 * The code is a direct translation from an earlier version written
 * in DML, the predessor of ATS.
 *
 * Hongwei Xi (January 2008)
 *
 *)

//

staload ARR = "prelude/DATS/array.dats"

//

typedef matrix (a:t@ype, m: int, n:int) = array (array (a, n), m)

fn{a:t@ype} sub2 {m,n:nat}
  (M: matrix (a, m, n), i: natLt m, j: natLt n): a =
  let val row = M[i] in row[j] end

fn{a:t@ype} update2 {m,n:nat}
  (M: matrix (a, m, n), i: natLt m, j: natLt n, x: a): void =
  let val row = M[i] in row[j] := x end

overload [] with sub2
overload [] with update2

(* ****** ****** *)

fn{a:t@ype} rowSwap (M, i, j) =
  let val tmp = M[i] in M[i] := M[j]; M[j] := tmp end
withtype {m,n:nat} {i,j:nat | i < m; j < m}
  (matrix (a, m, n), int i, int j) -<fun1> void

fn norm  {n,i:nat | i < n}
  (r: array(double, n), n: int n, i: int i): void = let
  val x = r[i]; val () = r[i] := 1.0
  fun loop {k:nat | k <= n} (k: int k):<cloptr1> void =
    if k < n then (r[k] := r[k] / x; loop (k+1)) else ()
in
  loop (i+1)
end

fn rowElim {n,i:nat | i < n}
  (r: array(double, n), s: array(double, n), n: int n, i: int i): void =
  let
    val x = s[i]; val () = s[i] := 0.0
    fun loop {k:nat | k <= n} (k: int k):<cloptr1> void =
      if k < n then (s[k] := s[k] - x * r[k]; loop (k+1)) else ()
  in
    loop (i+1)
  end		

fn rowMax {m,n,i:nat | i < m; i < n}
  (M: matrix (double, m, n), m: int m, i: int i): natLt m =
  let
    val x = abs (M[i,i])
    fun loop {j,max:nat | max < j; j <= m} .<m-j>.
      (j: int j, x: double, max: int max):<cloptr1> natLt m =
      if j < m then let
        val y = abs (M[j,i])
     in
        if (y > x) then loop (j+1, y, j) else loop (j+1, x, max)
     end else begin
       max // the return value of the loop
     end
  in
    loop (i + 1, x, i)
  end

fn GaussElim {n:nat}
  (M: matrix (double, n, n+1), n: int n): void = let
  fun loop1 {i:nat | i <= n} .<n-i>. (i: int i):<cloptr1> void =
    if i < n then let
      val max = rowMax(M, n, i)
      val () = norm (M[max], n+1, i)
      val () = rowSwap (M, i, max)
      val () = loop2 (i+1) where {
        fun loop2 {j:nat | j <= n} .<n-j>. (j: int j):<cloptr1> void =
          if j < n then (rowElim (M[i], M[j], n+1, i); loop2 (j+1))
      } // end of [where]
    in
      loop1 (i+1)
    end
in
  loop1 (0)
end // end of [GaussElim]

fun print_array {n,i,j:nat | i <= j; j <= n} .<j-i>.
  (A: array (double, n), i: int i, j: int j): void = let
  fun loop {k:int | i < k; k <= j} (k: int k):<cloptr1> void =
    if k < j then (print "\t"; print A[k]; loop (k+1)) else print_newline ()
in
  if i < j then (print A[i]; loop (i+1)) else print_newline ()
end

fn print_matrix {m,n:nat} (M: matrix(double, m, n)): void = let
  val m = length M
  fun loop {i:nat | i <= m} .<m-i>. (i: int i):<cloptr1> void =
    if i < m then let
      val row = M[i]; val () = print_array (row, 0, length row)
    in
      loop (i+1)
    end
in
  loop (0)
end // end of [print_matrix]

(* Here is a test *)

implement main (argc, argv) = let
val A0 = array_make_elt<double> (4, 0.0)

val M0: matrix (double, 3, 4) = array_make_elt (3, A0)
val () = M0[0,0] := 1.0
val () = M0[0,1] := 1.0
val () = M0[0,2] := 1.0
val () = M0[0,3] := ~4.0

val () = M0[1] := array_make_elt<double> (4, 0.0)
val () = M0[1,0] := ~2.0
val () = M0[1,1] := 3.0
val () = M0[1,2] := 1.0
val () = M0[1,3] := 7.0

val () = M0[2] := array_make_elt<double> (4, 0.0)
val () = M0[2,0] := 3.0
val () = M0[2,1] := ~1.0
val () = M0[2,2] := 2.0
val () = M0[2,3] := 7.0

// (-9, -8, 13) is the solution to the 1st, 2nd and 3rd variables.

in

print_matrix M0;
GaussElim (M0, 3);
print_matrix M0;

end

(* ****** ****** *)

(* end of [GaussElim.dats] *)
