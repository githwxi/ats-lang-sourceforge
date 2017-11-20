//
// K&R, 2nd edition, pages 186 - 188
//

// Translated to ATS by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2009

(* ****** ****** *)

absview Header_v
  (addr(*beg*), addr(*end*), int(*size*), addr(*nxt*))
// end of [Header/4]

viewdef Header_v
  (l_beg:addr, l_end:addr, sz:int) =
  [l_nxt:addr] Header_v (l_beg, l_end, sz, l_nxt)
// end of [Header_v/3]

extern fun Header_get_end
  {l_beg,l_end:addr} {sz:nat} {l_nxt:addr}
  (pf: !Header_v (l_beg, l_end, sz, l_nxt) | p: ptr l_beg):<> ptr (l_end)
// end of [Header_get_end]

extern fun Header_get_size
  {l_beg,l_end:addr} {sz:nat} {l_nxt:addr}
  (pf: !Header_v (l_beg, l_end, sz, l_nxt) | p: ptr l_beg):<> size_t (sz)
// end of [Header_get_size]

extern fun Header_get_nxt
  {l_beg,l_end:addr} {sz:nat} {l_nxt:addr}
  (pf: !Header_v (l_beg, l_end, sz, l_nxt) | p: ptr l_beg):<> ptr (l_nxt)
// end of [Header_get_nxt]

extern fun Header_set_nxt
  {l_beg,l_end:addr} {sz:nat} {l_nxt:addr} (
    pf: !Header_v (l_beg, l_end, sz) >> Header_v (l_beg, l_end, sz, l_nxt)
  | p: ptr l_beg, p1: ptr l_nxt
  ) :<> void
// end of [Header_set_nxt]

extern fun Header_split
  {l_beg,l_end:addr} {sz,sz1:nat | sz1 < sz} {l_nxt:addr} (
    pf: !Header_v (l_beg, l_end, sz, l_nxt) >> Header_v (l_beg, l, sz-sz1-1, l_nxt)
  | p: ptr l_beg
  ) :<> #[l:addr] (Header_v (l, l_end, sz1) | ptr l)

(* ****** ****** *)

dataview HeaderSeg_v (
  addr(*beg*), addr(*end*), int(*len*)
) =
  | {l0,l1:addr}
    {n:nat;sz:pos}
    {l0_end,l0_nxt:addr | l0_nxt == null || l0_end < l0_nxt}
    HeaderSeg_v_cons (l0, l1, n+1) of
      (Header_v (l0, l0_end, sz, l0_nxt), HeaderSeg_v (l0_nxt, l1, n))
  | {l:addr} HeaderSeg_v_nil (l, l, 0)
// end of [HeaderSeg_v]

(* ****** ****** *)
////
extern fun HeaderSeg_insert {l0,l1:addr} {n,ss:nat}
  {l_beg,l_end:addr} {s:pos} {l_nxt:addr}
  (pf1: HeaderSeg_v (l0, l1, n, ss), pf2: Header_v (l_beg, l_end, s, l_nxt))
  :<> [l0:addr] [n1:nat | n1 <= n+1] HeaderSeg_v (l0, l1, n1, ss+s)
////


(* ****** ****** *)

extern fun malloc {n:nat} (n: size_t n)
  :<> [l:addr] (option_v (b0ytes n @ l, l <> null) | ptr l)
// end of [malloc]

(* ****** ****** *)

(* end of [malloc_mfree.dats] *)
