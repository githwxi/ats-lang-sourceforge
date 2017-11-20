(*
**
** A hashtable implementation
** where buckets are represented as linked lists
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: August, 2009
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

typedef hash (key: t@ype) = (key) -<cloref> ulint
typedef eq (key: t@ype) = (key, key) -<cloref> bool

(* ****** ****** *)

extern
fun{key:t@ype} equal_key_key (x1: key, x2: key, eq: eq key):<> bool
// end of [extern]

implement{key} equal_key_key (x1, x2, eq) = eq (x1, x2)

(* ****** ****** *)

extern
fun{key:t@ype} hash_key (x: key, hash: hash key):<> ulint
// end of [extern]

implement{key} hash_key (x, hash) = hash (x)

(* ****** ****** *)

sortdef t0p = t@ype and vt0p = viewt@ype

(* ****** ****** *)

viewtypedef bucket (
  key:t0p, itm:vt0p, l:addr
) = @{
  key= key, itm= itm, nxt= ptr l
} // end of [node]

viewtypedef bucket (
  key:t0p, itm:vt0p
) = @{
  key= key, itm= itm, nxt= ptr?
} // end of [node]

absviewtype hashtbl_vt (key:t0p, itm:vt0p, sz:int)

(* ****** ****** *)

extern fun hashtbl_make {key:t0p;itm:vt0p} {sz:pos} {l:addr}
  (pf: @[ptr?][sz] @ l | p: ptr l, sz: size_t sz):<> hashtbl_vt (key, itm, sz)
  = "hashtbl_make"
// end of [hashtbl_make]

(* ****** ****** *)

extern
fun{key:t0p;itm:t0p}
  hashtbl_search {sz:int | sz > 0}  (
    tbl: !hashtbl_vt (key, itm, sz), sz: size_t sz, k0: key
  , res: &itm? >> opt (itm, tag), hash: hash key, eq: eq key
  ) :<> #[tag:two] int (tag)
// end of [hashtbl_search]

extern
fun{key:t0p;itm:vt0p}
  hashtbl_insert {sz:int | sz > 0} {l_at:addr} (
    pf_at: bucket (key, itm) @ l_at
  | tbl: !hashtbl_vt (key, itm, sz), sz: size_t sz, p_at: ptr l_at
  , hash: hash key, eq: eq key
  ) :<> void
// end of [hashtbl_insert]

extern
fun{key:t0p;itm:vt0p}
  hashtbl_remove {sz:int | sz > 0} {l_at:addr} (
    tbl: !hashtbl_vt (key, itm, sz), sz: size_t sz, k0: key
  , hash: hash key, eq: eq key
  ) :<> [l_at:addr] (
    option_v (bucket (key, itm) @ l_at, l_at <> null) | ptr l_at
  )
// end of [hashtbl_remove]

(* ****** ****** *)

dataview chain_v (
  key:t@ype, itm:viewt@ype+, int(*len*), addr(*loc*)
) =
  | {n:nat} {l0,l1:addr | l0 <> null}
    chain_v_cons (key, itm, n+1, l0) of
      (bucket (key, itm, l1) @ l0, chain_v (key, itm, n, l1))
  | chain_v_nil (key, itm, 0, null)
// end of [chain_v]

viewtypedef chain_vt
  (key:t0p, itm:vt0p, n:int) = [l:addr] (chain_v (key, itm, n, l) | ptr l)
// end of [chain_vt]

(* ****** ****** *)

(*

// for the purpose of debugging
extern fun{key:t0p} prerr_key (k: key): void
extern fun{itm:t0p} prerr_itm (i: itm): void

*)

(* ****** ****** *)

fun{key:t0p;itm:t0p}
  chain_search {n:nat} {l:addr} .<n>. (
    pf_kis: !chain_v (key,itm,n,l)
  | p_kis: ptr l, k0: key, res: &itm? >> opt (itm, tag), eq: eq key
  ) :<> #[tag:two] int (tag) =
  if p_kis <> null then let
    prval chain_v_cons (pf_ki, pf1_kis) = pf_kis
    val keq = equal_key_key (k0, p_kis->key, eq)
  in
    if keq then let
      val () = res := p_kis->itm
      prval () = opt_some {itm} (res)
      prval () = pf_kis := chain_v_cons (pf_ki, pf1_kis)
    in
      1 // [k0] is found
    end else let
      val tag = chain_search (pf1_kis | p_kis->nxt, k0, res, eq)
      prval () = pf_kis := chain_v_cons (pf_ki, pf1_kis)
    in
      tag
    end // end of [if]
  end else let
    prval () = opt_none {itm} (res) in 0 // [k0] is not found
  end // end of [if]
// end of [chain_search]

(* ****** ****** *)

stadef l2i (l: addr) = int_of_bool (l <> null)

fun{key:t0p;itm:vt0p}
  chain_remove {n:nat} {l0:addr} .<n>. (
    pf_kis: !chain_v (key, itm, n, l0) >> chain_v (key, itm, n1, l1)
  | p_kis: &ptr l0 >> ptr l1
  , k0: key
  , eq: eq key
  ) :<> #[n1:nat;l1:addr] [l_at:addr | n == n1 + l2i l_at] (
    option_v (bucket (key, itm) @ l_at, l_at <> null) | ptr l_at
  ) = let
  val p = p_kis
in
  if p <> null then let
    prval chain_v_cons (pf_bkt, pf1_kis) = pf_kis
    val keq = equal_key_key (k0, p->key, eq)
  in
    if keq then let
      viewdef V = bucket (key, itm) @ l0
      prval () = pf_kis := pf1_kis; val () = p_kis := p->nxt
    in
      (Some_v {V} (pf_bkt) | p) // removal
    end else let
      val ans = chain_remove<key,itm> {n-1} (pf1_kis | p->nxt, k0, eq) // tail-call
      prval () = pf_kis := chain_v_cons (pf_bkt, pf1_kis)
    in
      ans
    end // end of [if]
  end else let
    viewdef V = bucket (key, itm) @ null
  in
    (None_v {V} () | null) // [k0] is not found
  end // end of [if]
end (* end of [chain_remove] *)

(* ****** ****** *)

stadef chainsz = sizeof (ptr)

dataview hashtbl_v // it is just an array of chains
  (key:t@ype, itm:viewt@ype+, int(*sz*), int(*tot*), addr, addr) =
  | {sz,tot,n:nat} {l_beg,l_end:addr}
    hashtbl_v_cons (key, itm, sz+1, tot+n, l_beg, l_end) of
      (chain_vt (key, itm, n) @ l_beg, hashtbl_v (key, itm, sz, tot, l_beg+chainsz, l_end))
  | {l:addr} hashtbl_v_nil (key, itm, 0, 0, l, l)
// end of [hashtbl_v]

(* ****** ****** *)

extern prfun hashtbl_v_split // proof is omitted
  {key:t0p;itm:vt0p} {sz,sz1,tot:nat | sz1 <= sz} {l_beg,l_end:addr} {ofs:int} (
    pf_mul: MUL (sz1, chainsz, ofs), pf_tbl: hashtbl_v (key, itm, sz, tot, l_beg, l_end)
  ) :<> [tot1:nat | tot1 <= tot] @(
    hashtbl_v (key, itm, sz1, tot1, l_beg, l_beg+ofs)
  , hashtbl_v (key, itm, sz-sz1, tot-tot1, l_beg+ofs, l_end)
  ) // end of [hashtbl_v_split]

extern prfun hashtbl_v_unsplit // proof is omitted
  {key:t0p;itm:vt0p} {sz1,sz2,tot1,tot2:nat} {l_beg,l_mid,l_end:addr} (
    pf1: hashtbl_v (key, itm, sz1, tot1, l_beg, l_mid), pf2: hashtbl_v (key, itm, sz2, tot2, l_mid, l_end)
  ) :<prf> hashtbl_v (
    key, itm, sz1+sz2, tot1+tot2, l_beg, l_end
  ) // end of [hashtbl_v_unsplit]

fn{key:t0p;itm:vt0p} hashtbl_ptr_split 
  {sz,sz1,tot:nat | sz1 <= sz} {l_beg,l_end:addr} (
    pf_tbl: hashtbl_v (key, itm, sz, tot, l_beg, l_end)
  | p_beg: ptr l_beg, sz1: size_t sz1
  ) :<> [tot1:nat | tot1 <= tot] [l_mid:addr] @(
    hashtbl_v (key, itm, sz1, tot1, l_beg, l_mid)
  , hashtbl_v (key, itm, sz-sz1, tot-tot1, l_mid, l_end)
  | ptr l_mid
  ) = let
  val (pf_mul | ofs) = mul2_size1_size1 (sz1, sizeof<ptr>)
  prval (pf1_tbl, pf2_tbl) = hashtbl_v_split {key,itm} (pf_mul, pf_tbl)
in
  (pf1_tbl, pf2_tbl | p_beg + ofs)
end // end of [hashtbl_ptr_split]

(* ****** ****** *)

extern castfn size1_of_ulint (x: ulint):<> [i:nat] size_t i

(* ****** ****** *)

assume hashtbl_vt (key:t0p, itm:vt0p, sz:int) =
  [tot:nat;l_beg,l_end:addr] (hashtbl_v (key, itm, sz, tot, l_beg, l_end) | ptr l_beg)
// end of [hashtbl_vt]

(* ****** ****** *)

implement{key,itm}
  hashtbl_search (tbl, sz, k0, res, hash, eq) = let
  val h = hash_key (k0, hash)
  val h = size1_of_ulint (h); val ofs = mod1_size1_size1 (h, sz)
  val (pf1, pf2 | p_mid) = hashtbl_ptr_split<key,itm> (tbl.0 | tbl.1, ofs)
  prval hashtbl_v_cons (pf21, pf22) = pf2
  val tag = chain_search (p_mid->0 | p_mid->1, k0, res, eq)
  prval pf2 = hashtbl_v_cons (pf21, pf22)
  prval () = tbl.0 := hashtbl_v_unsplit (pf1, pf2)
in
  tag (* 0/1 : found/notfound *)
end // end of [hashtbl_search]

(* ****** ****** *)

implement{key,itm}
  hashtbl_insert (pf_at | tbl, sz, p_at, hash, eq) = let
//
  prval () = lemma (pf_at) where {
    extern prfun lemma {l_at:addr} (pf: !bucket (key, itm) @ l_at): [l_at <> null] void
  } // end of [prval]
//
  val h = hash_key (p_at->key, hash)
  val h = size1_of_ulint (h); val ofs = mod1_size1_size1 (h, sz)
  val (pf1_tbl, pf2_tbl | p_mid) = hashtbl_ptr_split<key,itm> (tbl.0 | tbl.1, ofs)
  prval hashtbl_v_cons (pf21_lst, pf22_tbl) = pf2_tbl
  val () = p_at->nxt := p_mid->1
  prval () = p_mid->0 := chain_v_cons (pf_at, p_mid->0)
  val () = p_mid->1 := p_at
  prval pf2_tbl = hashtbl_v_cons (pf21_lst, pf22_tbl)
  prval () = tbl.0 := hashtbl_v_unsplit (pf1_tbl, pf2_tbl)
in
  // nothing
end // end of [hashtbl_insert]

(* ****** ****** *)

implement{key,itm}
  hashtbl_remove (tbl, sz, k0, hash, eq) = let
  val h = hash_key (k0, hash)
  val h = size1_of_ulint (h); val ofs = mod1_size1_size1 (h, sz)
  val (pf1_tbl, pf2_tbl | p_mid) = hashtbl_ptr_split<key,itm> (tbl.0 | tbl.1, ofs)
  prval hashtbl_v_cons (pf21_lst, pf22_tbl) = pf2_tbl
  val ans = chain_remove (p_mid->0 | p_mid->1, k0, eq)
  prval pf2_tbl = hashtbl_v_cons (pf21_lst, pf22_tbl)
  prval () = tbl.0 := hashtbl_v_unsplit (pf1_tbl, pf2_tbl)
in
  ans
end // end of [hashtbl_remove]

(* ****** ****** *)

%{$

// shortcuts? yes. worth it? probably.

// static inline
ats_ptr_type hashtbl_make (
  ats_ptr_type p_tbl, ats_size_type sz
) {
  memset (p_tbl, 0/*NULL*/, sz * sizeof(ats_ptr_type)) ; return p_tbl ;
} /* end of [hashtbl_make] */

%}

(* ****** ****** *)

(* end of [hashtable_ngc.dats] *)
