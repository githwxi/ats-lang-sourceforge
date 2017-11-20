(*
main.atxt: 17(line=2, offs=1) -- 60(line=4, offs=3)
*)

#include "./../MYTEXT/mytextfun.hats"

(*
main.atxt: 184(line=10, offs=2) -- 200(line=10, offs=18)
*)
val __tok1 = patscode_style()
val () = theAtextMap_insert_str ("__tok1", __tok1)

(*
main.atxt: 202(line=11, offs=2) -- 218(line=11, offs=18)
*)
val __tok2 = patspage_style()
val () = theAtextMap_insert_str ("__tok2", __tok2)

(*
main.atxt: 743(line=35, offs=2) -- 778(line=37, offs=3)
*)
val __tok3 = pats2xhtml_sats("\
abstype myseq
")
val () = theAtextMap_insert_str ("__tok3", __tok3)

(*
main.atxt: 873(line=43, offs=2) -- 927(line=45, offs=3)
*)
val __tok4 = pats2xhtml_sats("\
fun mergesort (xs: myseq): myseq
")
val () = theAtextMap_insert_str ("__tok4", __tok4)

(*
main.atxt: 1034(line=51, offs=2) -- 1295(line=64, offs=3)
*)
val __tok5 = pats2xhtml_dats("\
implement
mergesort (xs) = let
  val n = myseq_length (xs)
in
//
  if n >= 2 then let
    val (xs1, xs2) = myseq_split (xs)
  in
    myseq_merge (mergesort (xs1), mergesort (xs2))
  end else (xs) // end of [if]
//
end // end of [mergesort]
")
val () = theAtextMap_insert_str ("__tok5", __tok5)

(*
main.atxt: 1431(line=71, offs=2) -- 1578(line=75, offs=3)
*)
val __tok6 = pats2xhtml_sats("\
fun myseq_length (xs: myseq): int
fun myseq_split (xs: myseq): (myseq, myseq)
fun myseq_merge (xs1: myseq, xs2: myseq): myseq
")
val () = theAtextMap_insert_str ("__tok6", __tok6)

(*
main.atxt: 2674(line=108, offs=2) -- 2716(line=110, offs=3)
*)
val __tok7 = pats2xhtml_sats("\
abstype myseq(n:int)
")
val () = theAtextMap_insert_str ("__tok7", __tok7)

(*
main.atxt: 2974(line=119, offs=2) -- 3041(line=121, offs=3)
*)
val __tok8 = pats2xhtml_sats("\
fun mergesort{n:nat} (xs: myseq(n)): myseq(n)
")
val () = theAtextMap_insert_str ("__tok8", __tok8)

(*
main.atxt: 3204(line=128, offs=2) -- 3454(line=137, offs=3)
*)
val __tok9 = pats2xhtml_sats("\
//
fun myseq_length{n:int} (xs: myseq(n)): int(n)
//
fun myseq_split{n:int | n >= 2}
  (xs: myseq(n)): [n1,n2:pos | n1+n2==n] (myseq(n1), myseq(n2))
//
fun myseq_merge{n1,n2:nat} (xs1: myseq(n1), xs2: myseq(n2)): myseq(n1+n2)
//
")
val () = theAtextMap_insert_str ("__tok9", __tok9)

(*
main.atxt: 3815(line=150, offs=2) -- 4163(line=171, offs=3)
*)
val __tok10 = pats2xhtml_dats("\
implement
mergesort (xs) = let
//
fun sort
  {n:nat} .<n>.
(
  xs: myseq(n)
) : myseq(n) = let
  val n = myseq_length (xs)
in
  if n >= 2 then let
    val (xs1, xs2) = myseq_split (xs)
  in
    myseq_merge (sort (xs1), sort (xs2))
  end else (xs) // end of [if]
end // end of [sort]
//
in
  sort (xs)
end // end of [mergesort]
")
val () = theAtextMap_insert_str ("__tok10", __tok10)

(*
main.atxt: 4458(line=183, offs=2) -- 4566(line=186, offs=3)
*)
val __tok11 = pats2xhtml_sats("\
fun myseq_split{n:int | n >= 2}
  (xs: myseq(n), n: int n): (myseq(n/2), myseq(n-n/2))
")
val () = theAtextMap_insert_str ("__tok11", __tok11)

(*
main.atxt: 4839(line=195, offs=2) -- 5222(line=216, offs=3)
*)
val __tok12 = pats2xhtml_dats("\
implement
mergesort (xs) = let
//
fun sort
  {n:nat} .<n>.
(
  xs: myseq(n), n: int n
) : myseq(n) = let
in
  if n >= 2 then let
    val n2 = half (n)
    val (xs1, xs2) = myseq_split (xs, n)
  in
    myseq_merge (sort (xs1, n2), sort (xs2, n-n2))
  end else (xs) // end of [if]
end // end of [sort]
//
in
  sort (xs, myseq_length(xs))
end // end of [mergesort]
")
val () = theAtextMap_insert_str ("__tok12", __tok12)

(*
main.atxt: 5574(line=231, offs=2) -- 5654(line=234, offs=3)
*)
val __tok13 = pats2xhtml_sats("\
fun{a:t0p}
mergesort{n:nat} (xs: list (a, n)): list (a, n)
")
val () = theAtextMap_insert_str ("__tok13", __tok13)

(*
main.atxt: 5905(line=243, offs=2) -- 6042(line=249, offs=3)
*)
val __tok14 = pats2xhtml_sats("\
fun{a:t0p}
myseq_merge
  {n1,n2:nat}
  (xs1: list(a, n1), xs2: list(a, n2)): list(a, n1+n2)
// end of [myseq_merge]
")
val () = theAtextMap_insert_str ("__tok14", __tok14)

(*
main.atxt: 6149(line=255, offs=2) -- 6642(line=279, offs=3)
*)
val __tok15 = pats2xhtml_dats("\
implement
{a}(*tmp*)
myseq_merge
  (xs10, xs20) = let
in
//
case+ xs10 of
| cons (x1, xs11) =>
  (
    case+ xs20 of
    | cons (x2, xs21) => let
        val sgn = gcompare_val<a> (x1, x2)
      in
        if sgn <= 0
          then cons{a}(x1, myseq_merge<a> (xs11, xs20))
          else cons{a}(x2, myseq_merge<a> (xs10, xs21))
        // end of [if]
      end (* end of [cons] *)
    | nil ((*void*)) => xs10
  )
| nil ((*void*)) => xs20
//
end // end of [myseq_merge]
")
val () = theAtextMap_insert_str ("__tok15", __tok15)

(*
main.atxt: 7329(line=306, offs=2) -- 7425(line=309, offs=3)
*)
val __tok16 = pats2xhtml_sats("\
fun{a:t0p}
mergesort{n:nat} (xs: arrayref(a, n), n: int n): arrayref(a, n)
")
val () = theAtextMap_insert_str ("__tok16", __tok16)

(*
main.atxt: 7627(line=320, offs=2) -- 7805(line=327, offs=3)
*)
val __tok17 = pats2xhtml_sats("\
fun{a:t0p}
myseq_merge
  {n1,n2:nat}
(
  xs1: arrayref(a, n1), xs2: arrayref(a, n2), n1: int(n1), n2: int(n2)
) : arrayref(a, n1+n2) // end of [myseq_merge]
")
val () = theAtextMap_insert_str ("__tok17", __tok17)

(*
main.atxt: 9142(line=361, offs=2) -- 9159(line=361, offs=19)
*)
val __tok18 = patspage_script()
val () = theAtextMap_insert_str ("__tok18", __tok18)

(*
main.atxt: 9177(line=365, offs=1) -- 9246(line=367, offs=3)
*)

implement main () = fprint_filsub (stdout_ref, "main_atxt.txt")

