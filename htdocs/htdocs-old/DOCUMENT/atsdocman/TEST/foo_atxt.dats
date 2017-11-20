(*
foo.atxt: 10(line=1, offs=10) -- 18(line=1, offs=18)
*)
val _tok1 = author()
val () = theTextMap_insert_str ("_tok1", _tok1)

(*
foo.atxt: 51(line=2, offs=33) -- 67(line=2, offs=49)
*)
val NOW = timestamp()
val () = theTextMap_insert_str ("NOW", NOW)

