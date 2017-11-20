(*
foo2.atxt: 1(line=1, offs=1) -- 90(line=6, offs=3)
*)

//
dynload "libatsdoc/dynloadall.dats"
//
staload "libatsdoc/SATS/atsdoc_text.sats"

(*
foo2.atxt: 92(line=8, offs=1) -- 133(line=10, offs=3)
*)

fn author () = TEXTstrcst"John Doe"

(*
foo2.atxt: 135(line=12, offs=1) -- 458(line=27, offs=3)
*)

staload
UN = "prelude/SATS/unsafe.sats"
staload TIME = "libc/SATS/time.sats"

fn timestamp
  (): text = let
  var time = $TIME.time_get ()
  val (fpf | x) = $TIME.ctime (time)
  val x1 = sprintf ("%s", @($UN.castvwtp1(x)))
  prval () = fpf (x)
  val x1 = string_of_strptr (x1)
in
  TEXTstrcst (x1)
end // end of [val]

(*
foo2.atxt: 469(line=29, offs=10) -- 477(line=29, offs=18)
*)
val _tok1 = author()
val () = theTextMap_insert_str ("_tok1", _tok1)

(*
foo2.atxt: 510(line=30, offs=33) -- 526(line=30, offs=49)
*)
val NOW = timestamp()
val () = theTextMap_insert_str ("NOW", NOW)

(*
foo2.atxt: 528(line=32, offs=1) -- 597(line=34, offs=3)
*)

implement main () = fprint_filsub (stdout_ref, "foo2_atxt.txt")

