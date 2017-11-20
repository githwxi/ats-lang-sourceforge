(*
main.atxt: 1(line=1, offs=1) -- 42(line=3, offs=3)
*)

#include "./../ATEXT/atextfun.hats"

(*
main.atxt: 186(line=13, offs=2) -- 202(line=13, offs=18)
*)
val __tok1 = patscode_style()
val () = theAtextMap_insert_str ("__tok1", __tok1)

(*
main.atxt: 204(line=14, offs=2) -- 220(line=14, offs=18)
*)
val __tok2 = patspage_style()
val () = theAtextMap_insert_str ("__tok2", __tok2)

(*
main.atxt: 531(line=28, offs=45) -- 558(line=28, offs=72)
*)
val __tok3 = filename("prop-logic.sats")
val () = theAtextMap_insert_str ("__tok3", __tok3)

(*
main.atxt: 564(line=29, offs=6) -- 591(line=29, offs=33)
*)
val __tok4 = filename("prop-logic.dats")
val () = theAtextMap_insert_str ("__tok4", __tok4)

(*
main.atxt: 685(line=38, offs=28) -- 701(line=38, offs=44)
*)
val __tok5 = stacode("PTRUE")
val () = theAtextMap_insert_str ("__tok5", __tok5)

(*
main.atxt: 707(line=38, offs=50) -- 724(line=38, offs=67)
*)
val __tok6 = stacode("PFALSE")
val () = theAtextMap_insert_str ("__tok6", __tok6)

(*
main.atxt: 752(line=42, offs=2) -- 827(line=45, offs=3)
*)
val __tok7 = pats2xhtml_sats("\
absprop PTRUE // for true
absprop PFALSE // for false
")
val () = theAtextMap_insert_str ("__tok7", __tok7)

(*
main.atxt: 895(line=47, offs=61) -- 910(line=47, offs=76)
*)
val __tok8 = stacode("true")
val () = theAtextMap_insert_str ("__tok8", __tok8)

(*
main.atxt: 938(line=51, offs=2) -- 992(line=53, offs=3)
*)
val __tok9 = pats2xhtml_sats("\
praxi true_intr((*void*)): PTRUE
")
val () = theAtextMap_insert_str ("__tok9", __tok9)

(*
main.atxt: 1060(line=55, offs=61) -- 1076(line=55, offs=77)
*)
val __tok10 = stacode("false")
val () = theAtextMap_insert_str ("__tok10", __tok10)

(*
main.atxt: 1104(line=59, offs=2) -- 1165(line=61, offs=3)
*)
val __tok11 = pats2xhtml_sats("\
praxi false_elim{A:prop}(pf: PFALSE): A
")
val () = theAtextMap_insert_str ("__tok11", __tok11)

(*
main.atxt: 1192(line=63, offs=20) -- 1213(line=63, offs=41)
*)
val __tok12 = dyncode("false_elim")
val () = theAtextMap_insert_str ("__tok12", __tok12)

(*
main.atxt: 1274(line=64, offs=26) -- 1290(line=64, offs=42)
*)
val __tok13 = stacode("false")
val () = theAtextMap_insert_str ("__tok13", __tok13)

(*
main.atxt: 1353(line=72, offs=22) -- 1365(line=72, offs=34)
*)
val __tok14 = stacode("A")
val () = theAtextMap_insert_str ("__tok14", __tok14)

(*
main.atxt: 1375(line=72, offs=44) -- 1393(line=72, offs=62)
*)
val __tok15 = stacode("PNEG(A)")
val () = theAtextMap_insert_str ("__tok15", __tok15)

(*
main.atxt: 1415(line=73, offs=18) -- 1427(line=73, offs=30)
*)
val __tok16 = stacode("A")
val () = theAtextMap_insert_str ("__tok16", __tok16)

(*
main.atxt: 1455(line=77, offs=2) -- 1556(line=80, offs=3)
*)
val __tok17 = pats2xhtml_sats("\
absprop PNEG(A: prop) // for negation
propdef ~(A: prop) = PNEG(A) // shorthand
")
val () = theAtextMap_insert_str ("__tok17", __tok17)

(*
main.atxt: 1582(line=82, offs=19) -- 1595(line=82, offs=32)
*)
val __tok18 = stacode("~A")
val () = theAtextMap_insert_str ("__tok18", __tok18)

(*
main.atxt: 1616(line=82, offs=53) -- 1634(line=82, offs=71)
*)
val __tok19 = stacode("PNEG(A)")
val () = theAtextMap_insert_str ("__tok19", __tok19)

(*
main.atxt: 1732(line=87, offs=2) -- 1846(line=90, offs=3)
*)
val __tok20 = pats2xhtml_sats("\
praxi neg_intr{A:prop}(fpf: A -> PFALSE): ~A
praxi neg_elim{A:prop}(pf1: ~A, pf2: A): PFALSE
")
val () = theAtextMap_insert_str ("__tok20", __tok20)

(*
main.atxt: 1868(line=92, offs=15) -- 1887(line=92, offs=34)
*)
val __tok21 = dyncode("neg_intr")
val () = theAtextMap_insert_str ("__tok21", __tok21)

(*
main.atxt: 1900(line=92, offs=47) -- 1913(line=92, offs=60)
*)
val __tok22 = stacode("~A")
val () = theAtextMap_insert_str ("__tok22", __tok22)

(*
main.atxt: 1944(line=93, offs=28) -- 1956(line=93, offs=40)
*)
val __tok23 = stacode("A")
val () = theAtextMap_insert_str ("__tok23", __tok23)

(*
main.atxt: 1990(line=94, offs=5) -- 2006(line=94, offs=21)
*)
val __tok24 = stacode("false")
val () = theAtextMap_insert_str ("__tok24", __tok24)

(*
main.atxt: 2041(line=95, offs=2) -- 2060(line=95, offs=21)
*)
val __tok25 = dyncode("neg_elim")
val () = theAtextMap_insert_str ("__tok25", __tok25)

(*
main.atxt: 2085(line=95, offs=46) -- 2101(line=95, offs=62)
*)
val __tok26 = stacode("false")
val () = theAtextMap_insert_str ("__tok26", __tok26)

(*
main.atxt: 2141(line=96, offs=33) -- 2154(line=96, offs=46)
*)
val __tok27 = stacode("~A")
val () = theAtextMap_insert_str ("__tok27", __tok27)

(*
main.atxt: 2171(line=97, offs=2) -- 2183(line=97, offs=14)
*)
val __tok28 = stacode("A")
val () = theAtextMap_insert_str ("__tok28", __tok28)

(*
main.atxt: 2211(line=103, offs=15) -- 2230(line=103, offs=34)
*)
val __tok29 = dyncode("neg_elim")
val () = theAtextMap_insert_str ("__tok29", __tok29)

(*
main.atxt: 2236(line=103, offs=40) -- 2257(line=103, offs=61)
*)
val __tok30 = dyncode("false_elim")
val () = theAtextMap_insert_str ("__tok30", __tok30)

(*
main.atxt: 2318(line=104, offs=57) -- 2330(line=104, offs=69)
*)
val __tok31 = stacode("B")
val () = theAtextMap_insert_str ("__tok31", __tok31)

(*
main.atxt: 2363(line=105, offs=33) -- 2375(line=105, offs=45)
*)
val __tok32 = stacode("A")
val () = theAtextMap_insert_str ("__tok32", __tok32)

(*
main.atxt: 2392(line=106, offs=2) -- 2405(line=106, offs=15)
*)
val __tok33 = stacode("~A")
val () = theAtextMap_insert_str ("__tok33", __tok33)

(*
main.atxt: 2433(line=110, offs=2) -- 2550(line=117, offs=3)
*)
val __tok34 = pats2xhtml_dats("\
//
prfn
neg_elim2
  {A:prop}{B:prop}
  (pf1: A, pf2: ~A): B = false_elim(neg_elim(pf1, pf2))
//
")
val () = theAtextMap_insert_str ("__tok34", __tok34)

(*
main.atxt: 2625(line=126, offs=25) -- 2637(line=126, offs=37)
*)
val __tok35 = stacode("A")
val () = theAtextMap_insert_str ("__tok35", __tok35)

(*
main.atxt: 2643(line=126, offs=43) -- 2655(line=126, offs=55)
*)
val __tok36 = stacode("B")
val () = theAtextMap_insert_str ("__tok36", __tok36)

(*
main.atxt: 2665(line=126, offs=65) -- 2687(line=126, offs=87)
*)
val __tok37 = stacode("PCONJ(A, B)")
val () = theAtextMap_insert_str ("__tok37", __tok37)

(*
main.atxt: 2712(line=127, offs=21) -- 2724(line=127, offs=33)
*)
val __tok38 = stacode("A")
val () = theAtextMap_insert_str ("__tok38", __tok38)

(*
main.atxt: 2730(line=127, offs=39) -- 2742(line=127, offs=51)
*)
val __tok39 = stacode("B")
val () = theAtextMap_insert_str ("__tok39", __tok39)

(*
main.atxt: 2770(line=131, offs=2) -- 2879(line=135, offs=3)
*)
val __tok40 = pats2xhtml_sats("\
absprop
PCONJ(A: prop, B: prop)
propdef &&(A: prop, B: prop) = PCONJ(A, B) // shorthand
")
val () = theAtextMap_insert_str ("__tok40", __tok40)

(*
main.atxt: 2905(line=137, offs=19) -- 2922(line=137, offs=36)
*)
val __tok41 = stacode("A && B")
val () = theAtextMap_insert_str ("__tok41", __tok41)

(*
main.atxt: 2943(line=138, offs=2) -- 2965(line=138, offs=24)
*)
val __tok42 = stacode("PCONJ(A, B)")
val () = theAtextMap_insert_str ("__tok42", __tok42)

(*
main.atxt: 3081(line=143, offs=2) -- 3247(line=154, offs=3)
*)
val __tok43 = pats2xhtml_sats("\
//
praxi
conj_intr
  {A,B:prop} : (A, B) -> A && B
//
praxi
conj_elim_l{A,B:prop} : (A && B) -> A
praxi
conj_elim_r{A,B:prop} : (A && B) -> B
//
")
val () = theAtextMap_insert_str ("__tok43", __tok43)

(*
main.atxt: 3360(line=160, offs=2) -- 3486(line=167, offs=3)
*)
val __tok44 = pats2xhtml_dats("\
//
prfn
conj_commute
  {A,B:prop}(pf: A && B): B && A =
  conj_intr(conj_elim_r(pf), conj_elim_l(pf))
//
")
val () = theAtextMap_insert_str ("__tok44", __tok44)

(*
main.atxt: 3561(line=176, offs=25) -- 3573(line=176, offs=37)
*)
val __tok45 = stacode("A")
val () = theAtextMap_insert_str ("__tok45", __tok45)

(*
main.atxt: 3579(line=176, offs=43) -- 3591(line=176, offs=55)
*)
val __tok46 = stacode("B")
val () = theAtextMap_insert_str ("__tok46", __tok46)

(*
main.atxt: 3601(line=176, offs=65) -- 3623(line=176, offs=87)
*)
val __tok47 = stacode("PDISJ(A, B)")
val () = theAtextMap_insert_str ("__tok47", __tok47)

(*
main.atxt: 3648(line=177, offs=21) -- 3660(line=177, offs=33)
*)
val __tok48 = stacode("A")
val () = theAtextMap_insert_str ("__tok48", __tok48)

(*
main.atxt: 3666(line=177, offs=39) -- 3678(line=177, offs=51)
*)
val __tok49 = stacode("B")
val () = theAtextMap_insert_str ("__tok49", __tok49)

(*
main.atxt: 3706(line=181, offs=2) -- 3869(line=189, offs=3)
*)
val __tok50 = pats2xhtml_sats("\
dataprop
PDISJ(A: prop, B: prop) =
  | disj_intr_l(A, B) of (A)
  | disj_intr_r(A, B) of (B)
//
propdef ||(A: prop, B: prop) = PDISJ(A, B)
//
")
val () = theAtextMap_insert_str ("__tok50", __tok50)

(*
main.atxt: 3895(line=191, offs=19) -- 3912(line=191, offs=36)
*)
val __tok51 = stacode("A || B")
val () = theAtextMap_insert_str ("__tok51", __tok51)

(*
main.atxt: 3933(line=192, offs=2) -- 3955(line=192, offs=24)
*)
val __tok52 = stacode("PDISJ(A, B)")
val () = theAtextMap_insert_str ("__tok52", __tok52)

(*
main.atxt: 4063(line=197, offs=2) -- 4249(line=206, offs=3)
*)
val __tok53 = pats2xhtml_dats("\
//
prfn
disj_commute
  {A,B:prop}(pf0: A || B): B || A =
  case+ pf0 of
  | disj_intr_l(pf0_l) => disj_intr_r(pf0_l)
  | disj_intr_r(pf0_r) => disj_intr_l(pf0_r)
//
")
val () = theAtextMap_insert_str ("__tok53", __tok53)

(*
main.atxt: 4279(line=208, offs=23) -- 4301(line=208, offs=45)
*)
val __tok54 = dyncode("disj_intr_l")
val () = theAtextMap_insert_str ("__tok54", __tok54)

(*
main.atxt: 4307(line=209, offs=2) -- 4329(line=209, offs=24)
*)
val __tok55 = dyncode("disj_intr_r")
val () = theAtextMap_insert_str ("__tok55", __tok55)

(*
main.atxt: 4347(line=209, offs=42) -- 4363(line=209, offs=58)
*)
val __tok56 = stacode("PDISJ")
val () = theAtextMap_insert_str ("__tok56", __tok56)

(*
main.atxt: 4462(line=211, offs=21) -- 4482(line=211, offs=41)
*)
val __tok57 = dyncode("disj_elim")
val () = theAtextMap_insert_str ("__tok57", __tok57)

(*
main.atxt: 4567(line=216, offs=2) -- 4767(line=225, offs=3)
*)
val __tok58 = pats2xhtml_dats("\
//
prfn
disj_elim{A,B:prop}{C:prop}
  (pf0: A || B, fpf1: A -> C, fpf2: B -> C): C =
  case+ pf0 of
  | disj_intr_l(pf0_l) => fpf1(pf0_l)
  | disj_intr_r(pf0_r) => fpf2(pf0_r)
//
")
val () = theAtextMap_insert_str ("__tok58", __tok58)

(*
main.atxt: 4930(line=232, offs=2) -- 5357(line=254, offs=3)
*)
val __tok59 = pats2xhtml_dats("\
prfn
conj_disj_distribute
  {A,B,C:prop}
(
  pf0: A && (B || C)
) : (A && B) || (A && C) = let
//
val pf0_l = conj_elim_l(pf0)
val pf0_r = conj_elim_r(pf0)
//
in
//
case+ pf0_r of
| disj_intr_l(pf0_rl) =>
    disj_intr_l(conj_intr(pf0_l, pf0_rl))
  // end of [disj_intr_l]
| disj_intr_r(pf0_rr) =>
    disj_intr_r(conj_intr(pf0_l, pf0_rr))
  // end of [disj_intr_r]
//
end // end of [conj_disj_distribute]
")
val () = theAtextMap_insert_str ("__tok59", __tok59)

(*
main.atxt: 5432(line=263, offs=25) -- 5444(line=263, offs=37)
*)
val __tok60 = stacode("A")
val () = theAtextMap_insert_str ("__tok60", __tok60)

(*
main.atxt: 5450(line=264, offs=6) -- 5462(line=264, offs=18)
*)
val __tok61 = stacode("B")
val () = theAtextMap_insert_str ("__tok61", __tok61)

(*
main.atxt: 5472(line=264, offs=28) -- 5494(line=264, offs=50)
*)
val __tok62 = stacode("PIMPL(A, B)")
val () = theAtextMap_insert_str ("__tok62", __tok62)

(*
main.atxt: 5519(line=265, offs=21) -- 5531(line=265, offs=33)
*)
val __tok63 = stacode("B")
val () = theAtextMap_insert_str ("__tok63", __tok63)

(*
main.atxt: 5538(line=265, offs=40) -- 5550(line=265, offs=52)
*)
val __tok64 = stacode("A")
val () = theAtextMap_insert_str ("__tok64", __tok64)

(*
main.atxt: 5578(line=269, offs=2) -- 5700(line=277, offs=3)
*)
val __tok65 = pats2xhtml_sats("\
//
absprop
PIMPL(A: prop, B: prop)
//
infixr (->) ->>
propdef ->>(A: prop, B: prop) = PIMPL(A, B)
//
")
val () = theAtextMap_insert_str ("__tok65", __tok65)

(*
main.atxt: 5726(line=279, offs=19) -- 5759(line=279, offs=52)
*)
val __tok66 = stacode("A <tt>-&gt;&gt;</tt> B")
val () = theAtextMap_insert_str ("__tok66", __tok66)

(*
main.atxt: 5780(line=280, offs=6) -- 5802(line=280, offs=28)
*)
val __tok67 = stacode("PIMPL(A, B)")
val () = theAtextMap_insert_str ("__tok67", __tok67)

(*
main.atxt: 5904(line=285, offs=2) -- 6032(line=293, offs=3)
*)
val __tok68 = pats2xhtml_sats("\
//
praxi
impl_intr{A,B:prop}(pf: A -> B): A ->> B
//
praxi
impl_elim{A,B:prop}(pf1: A ->> B, pf2: A): B
//
")
val () = theAtextMap_insert_str ("__tok68", __tok68)

(*
main.atxt: 6054(line=295, offs=15) -- 6066(line=295, offs=27)
*)
val __tok69 = stacode("A")
val () = theAtextMap_insert_str ("__tok69", __tok69)

(*
main.atxt: 6077(line=295, offs=38) -- 6089(line=295, offs=50)
*)
val __tok70 = stacode("B")
val () = theAtextMap_insert_str ("__tok70", __tok70)

(*
main.atxt: 6132(line=296, offs=23) -- 6161(line=296, offs=52)
*)
val __tok71 = stacode("A <tt>-&gt;</tt> B")
val () = theAtextMap_insert_str ("__tok71", __tok71)

(*
main.atxt: 6199(line=302, offs=2) -- 6347(line=302, offs=150)
*)
val __tok72 = stacode("(A <tt>-&gt;&gt;</tt> (B <tt>-&gt;&gt;</tt> C)) <tt>-&gt;&gt;</tt> ((A <tt>-&gt;&gt;</tt> B) <tt>-&gt;&gt;</tt> (A <tt>-&gt;&gt;</tt> C))")
val () = theAtextMap_insert_str ("__tok72", __tok72)

(*
main.atxt: 6395(line=306, offs=2) -- 6660(line=322, offs=3)
*)
val __tok73 = pats2xhtml_dats("\
prfn
Subst{A,B,C:prop}
(
// argless
) : (A ->> (B ->> C)) ->> ((A ->> B) ->> (A ->> C)) =
impl_intr(
  lam pf1 =>
  impl_intr(
    lam pf2 =>
    impl_intr(
      lam pf3 =>
      impl_elim(impl_elim(pf1, pf3), impl_elim(pf2, pf3))
    )
  )
)
")
val () = theAtextMap_insert_str ("__tok73", __tok73)

(*
main.atxt: 6735(line=331, offs=25) -- 6747(line=331, offs=37)
*)
val __tok74 = stacode("A")
val () = theAtextMap_insert_str ("__tok74", __tok74)

(*
main.atxt: 6753(line=332, offs=6) -- 6765(line=332, offs=18)
*)
val __tok75 = stacode("B")
val () = theAtextMap_insert_str ("__tok75", __tok75)

(*
main.atxt: 6775(line=332, offs=28) -- 6798(line=332, offs=51)
*)
val __tok76 = stacode("PEQUIV(A, B)")
val () = theAtextMap_insert_str ("__tok76", __tok76)

(*
main.atxt: 6844(line=333, offs=38) -- 6856(line=333, offs=50)
*)
val __tok77 = stacode("A")
val () = theAtextMap_insert_str ("__tok77", __tok77)

(*
main.atxt: 6862(line=333, offs=56) -- 6874(line=333, offs=68)
*)
val __tok78 = stacode("B")
val () = theAtextMap_insert_str ("__tok78", __tok78)

(*
main.atxt: 6902(line=337, offs=2) -- 7001(line=341, offs=3)
*)
val __tok79 = pats2xhtml_sats("\
absprop
PEQUIV(A: prop, B: prop)
propdef == (A: prop, B: prop) = PEQUIV(A, B)
")
val () = theAtextMap_insert_str ("__tok79", __tok79)

(*
main.atxt: 7027(line=343, offs=19) -- 7044(line=343, offs=36)
*)
val __tok80 = stacode("A == B")
val () = theAtextMap_insert_str ("__tok80", __tok80)

(*
main.atxt: 7065(line=344, offs=2) -- 7088(line=344, offs=25)
*)
val __tok81 = stacode("PEQUIV(A, B)")
val () = theAtextMap_insert_str ("__tok81", __tok81)

(*
main.atxt: 7205(line=349, offs=2) -- 7391(line=360, offs=3)
*)
val __tok82 = pats2xhtml_sats("\
//
praxi
equiv_intr
  {A,B:prop}(A ->> B, B ->> A): A == B
//
praxi
equiv_elim_l{A,B:prop}(pf: A == B): A ->> B
praxi
equiv_elim_r{A,B:prop}(pf: A == B): B ->> A
//
")
val () = theAtextMap_insert_str ("__tok82", __tok82)

(*
main.atxt: 7526(line=371, offs=2) -- 7572(line=371, offs=48)
*)
val __tok83 = pats2xhtml_sats("praxi LDN{A:prop}(~(~A)): A")
val () = theAtextMap_insert_str ("__tok83", __tok83)

(*
main.atxt: 7708(line=383, offs=2) -- 7763(line=383, offs=57)
*)
val __tok84 = pats2xhtml_sats("praxi LEM{A:prop}((*void*)): A || ~A")
val () = theAtextMap_insert_str ("__tok84", __tok84)

(*
main.atxt: 7871(line=395, offs=2) -- 7950(line=398, offs=3)
*)
val __tok85 = pats2xhtml_sats("\
praxi
Peirce{P,Q:prop}((*void*)): ((P ->> Q) ->> P) ->> P
")
val () = theAtextMap_insert_str ("__tok85", __tok85)

(*
main.atxt: 8204(line=408, offs=2) -- 8221(line=408, offs=19)
*)
val __tok86 = patspage_script()
val () = theAtextMap_insert_str ("__tok86", __tok86)

(*
main.atxt: 8239(line=412, offs=1) -- 8308(line=414, offs=3)
*)

implement main () = fprint_filsub (stdout_ref, "main_atxt.txt")

