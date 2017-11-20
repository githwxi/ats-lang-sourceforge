staload Q = "linqueuelst.dats"
staload L = "prelude/DATS/list.dats"
staload P = "prelude/DATS/pointer.dats"

fun{a,b:t@ype} map {n:nat}
  (xs: list (a, n), f: a -> b): list (b, n) = let
  fun loop {m,n:nat} (
      xs: list (a, n)
    , que: & $Q.linqueuelst_vt (b, m) >> $Q.linqueuelst_vt (b, m+n)
    ) :<cloref1> void = begin case+ xs of
    | list_cons (x, xs) => begin
        let val () = $Q.linqueuelst_enqueue (que, f x) in loop (xs, que) end
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [loop]
  var que = $Q.linqueuelst_nil {b} ()
  val () = loop (xs, que)
  val que = $Q.list_vt_of_linqueuelst (que)
in
  list_of_list_vt (que)
end // end of [map]

val xs0 = '[0,1,2,3,4]: List int
val xs1 = map<int,int> (xs0, lam x => x + x)

prval pf = unit_v
val () = list_iforeach_cloref<int> {unit_v}
  (pf | xs1, lam (pf | i, x) =<cloref1> (if i > 0 then print ", "; print x))
val () = print_newline ()

implement main () = ()

