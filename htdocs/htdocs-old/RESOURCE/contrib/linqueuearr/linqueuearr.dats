(*
**
** An implementation of linear queues based on arrays
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

absviewtype linqueuearr_vt
  (a:viewt@ype (*element*), m:int (*max capacity*), n:int (*size*))

stadef queue = linqueuearr_vt // an abbreviation

(* ****** ****** *)

absview queuearr_v (
    viewt@ype+ (*element*)
  , int (*max*), int (*size*)
  , addr (*beg*), addr (*end*)
  , addr (*beginning of initialized/occupied segment*)
  , addr (*beginning of uninitialized/unoccupied segment*)
  ) // end of [queuearr_v]

extern fun queuearr_enqueue_takeout {a:viewt@ype}
  {m,n:nat | n < m} {l_beg,l_end:addr} {l_ini,l_uni:addr} (
    pf: queuearr_v (a, m, n, l_beg, l_end, l_ini, l_uni)
  | p_beg: ptr l_beg, p_end: ptr l_end, p_uni: ptr l_uni
  , tsz: sizeof_t (a)
  ) :<> [l_uni_new:addr] (
    a? @ l_uni
  , a @ l_uni -<lin,prf> queuearr_v (a, m, n+1, l_beg, l_end, l_ini, l_uni_new)
  | ptr l_uni_new
  ) // queuearr_enqueue_takeout
  = "linqueuearr_queuearr_enqueue_takeout"

extern fun queuearr_dequeue_takeout {a:viewt@ype}
  {m,n:nat | n > 0} {l_beg,l_end:addr} {l_ini,l_uni:addr} (
    pf: queuearr_v (a, m, n, l_beg, l_end, l_ini, l_uni)
  | p_beg: ptr l_beg, p_end: ptr l_end, p_ini: ptr l_ini
  , tsz: sizeof_t (a)
  ) :<> [l_ini_new:addr] (
    a @ l_ini
  , a? @ l_ini -<lin,prf> queuearr_v (a, m, n-1, l_beg, l_end, l_ini_new, l_uni)
  | ptr l_ini_new
  ) // queuearr_dequeue_takeout
  = "linqueuearr_queuearr_dequeue_takeout"

extern fun queuearr_free {a:viewt@ype}
  {m:nat} {l_beg,l_end:addr} {l_ini,l_uni:addr} (
    pf: queuearr_v (a, m, 0, l_beg, l_end, l_ini, l_uni) | p_beg: ptr l_beg
  ) :<> void
  = "linqueuearr_queuearr_free"

(* ****** ****** *)

%{^

// static inline
ats_ptr_type linqueuearr_queuearr_enqueue_takeout (
    ats_ptr_type p_beg
  , ats_ptr_type p_end
  , ats_ptr_type p_uni
  , ats_size_type tsz
  ) {
  ats_ptr_type p_uni_new = (ats_byte_type*)p_uni + tsz ;
  if (p_uni_new >= p_end) return p_beg ;
  return p_uni_new ;
}

// static inline
ats_ptr_type linqueuearr_queuearr_dequeue_takeout (
    ats_ptr_type p_beg
  , ats_ptr_type p_end
  , ats_ptr_type p_ini
  , ats_size_type tsz
  ) {
  ats_ptr_type p_ini_new = (ats_byte_type*)p_ini + tsz ;
  if (p_ini_new >= p_end) return p_beg ;
  return p_ini_new ;
}

// static inline
ats_void_type linqueuearr_queuearr_free (ats_ptr_type p_beg) {
  ATS_FREE (p_beg) ; return ; 
}

%} // end of [%{^]

(* ****** ****** *)

dataviewtype queuearr_vt
  (a:viewt@ype+, int(*max*), int(*size*)) =
  | {m:pos;n:nat | n <= m} {l_beg,l_end:addr} {l_ini,l_uni:addr}
    queuearr_vt_some (a, m, n) of (
      queuearr_v (a, m, n, l_beg, l_end, l_ini, l_uni)
    | int m, int n, ptr l_beg, ptr l_end, ptr l_ini, ptr l_uni
    ) // end of [queuearr_some]
  | queuearr_vt_none (a, 0, 0) of ()
// end of [queuearr_vt]

assume linqueuearr_vt (a: viewt@ype, m: int, n: int) = queuearr_vt (a, m, n)

(* ****** ****** *)

extern fun{a:viewt@ype}
  linqueuearr_make {m:nat} (m: int m):<> queue (a, m, 0)

(* ****** ****** *)

implement{a} linqueuearr_make {m} (m) =
  if m > 0 then let
    stadef tsz = sizeof a; val tsz = sizeof<a>
    val m_sz = size1_of_int1 m
    val [l:addr] (pf_gc, pf_arr | p) = array_ptr_alloc_tsz {a} (m_sz, tsz)
    val [ofs:int] (pf_mul | ofs) = mul2_size1_size1 (m_sz, tsz)
    prval pf = queuearr_v_of_array_v (pf_gc, pf_arr, pf_mul) where {
      extern prfun queuearr_v_of_array_v (
        pf_gc: free_gc_v (a, m, l), pf_arr: array_v (a?, m, l), pf_mul: MUL (m, tsz, ofs)
      ) : queuearr_v (a, m, 0, l, l+ofs, l, l)
    } // end of [where]
  in
    queuearr_vt_some (pf | m, 0, p, p+ofs, p, p)
  end else begin
    queuearr_vt_none () // m = 0
  end // end of [if]
// end of [linqueuearr_make]

(* ****** ****** *)

extern fun{} linqueuearr_max
  {a:viewt@ype} {m,n:nat} (xs: !queue (a, m(*max*), n(*size*))):<> int m

extern fun{} linqueuearr_size
  {a:viewt@ype} {m,n:nat} (xs: !queue (a, m(*max*), n(*size*))):<> int n

extern fun{} linqueuearr_isfull
  {a:viewt@ype} {m,n:nat} (xs: !queue (a, m(*max*), n(*size*))):<> bool (m==n)

(* ****** ****** *)

implement{} linqueuearr_max (xs) = case+ xs of
  | queuearr_vt_some
      (_ | m, _(*n*), _(*beg*), _(*end*), _(*ini*), _(*uni*)) => (fold@ xs; m)
  | queuearr_vt_none () => (fold@ xs; 0)
// end of [linqueuearr_max]

implement{} linqueuearr_size (xs) = case+ xs of
  | queuearr_vt_some
      (_ | _(*m*), n, _(*beg*), _(*end*), _(*ini*), _(*uni*)) => (fold@ xs; n)
  | queuearr_vt_none () => (fold@ xs; 0)
// end of [linqueuearr_size]

implement{} linqueuearr_isfull (xs) = case+ xs of
  | queuearr_vt_some
      (_ | m, n, _(*beg*), _(*end*), _(*ini*), _(*uni*)) => (fold@ xs; m = n)
  | queuearr_vt_none () => (fold@ xs; true)
// end of [linqueuearr_isfull]

(* ****** ****** *)

extern fun{a:viewt@ype} linqueuearr_enqueue
  {m,n:nat | n < m} (xs: !queue (a, m, n) >> queue (a, m, n+1), x: a):<> void

extern fun{a:viewt@ype} linqueuearr_dequeue
  {m,n:nat | n > 0} (xs: !queue (a, m, n) >> queue (a, m, n-1)):<> a

(* ****** ****** *)

implement{a:viewt@ype} linqueuearr_enqueue (xs, x) = let
  val+ queuearr_vt_some
    (!pf_r | _(*m*), !n_r, p_beg, p_end, _(*ini*), !p_uni_r) = xs
  val p_uni = !p_uni_r
  val (pf, fpf | p_uni_new) =
    queuearr_enqueue_takeout {a} (!pf_r | p_beg, p_end, p_uni, sizeof<a>)
in
  !p_uni := x; !n_r := !n_r + 1; !p_uni_r := p_uni_new; !pf_r := fpf pf; fold@ (xs)
end // end of [linqueuearr_enqueue]

implement{a:viewt@ype} linqueuearr_dequeue (xs) = let
  val+ queuearr_vt_some
    (!pf_r | _(*m*), !n_r, p_beg, p_end, !p_ini_r, _(*uni*)) = xs
  val p_ini = !p_ini_r
  val (pf, fpf | p_ini_new) =
    queuearr_dequeue_takeout {a} (!pf_r | p_beg, p_end, p_ini, sizeof<a>)
  val x = !p_ini
in
  !n_r := !n_r - 1; !p_ini_r := p_ini_new; !pf_r := fpf pf; fold@ (xs); x
end // end of [linqueuearr_dequeue]

(* ****** ****** *)

(* end of [linqueuearr.dats] *)
