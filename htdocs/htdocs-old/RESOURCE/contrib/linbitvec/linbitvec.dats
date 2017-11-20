(*
**
** An implementation of functional maps based on AVL trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: May, 2009
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

abst@ype bitvec_int_t0ype (n:int) // an abstract type of unspecified size 
stadef bitvec_t = bitvec_int_t0ype

(* ****** ****** *)

typedef bit = [b: two] int b // b=0 or b=1

(* ****** ****** *)

extern fun bitvec_make {n:nat}
  (n: size_t n):<> [l:addr] (free_gc_v l, bitvec_t (n) @ l | ptr l)
  = "linbitvec_bitvec_make"
// end of [bitvec_make]

extern fun bitvec_make_empty {n:nat}
  (n: size_t n):<> [l:addr] (free_gc_v l, bitvec_t (n) @ l | ptr l)
  = "linbitvec_bitvec_make_empty"
// end of [bitvec_make_empty]

extern fun bitvec_make_full {n:nat}
  (n: size_t n):<> [l:addr] (free_gc_v l, bitvec_t (n) @ l | ptr l)
  = "linbitvec_bitvec_make_full"
// end of [bitvec_make_full]

extern fun bitvec_free {n:nat} {l:addr}
  (pf_gc: free_gc_v l, pf_vec: bitvec_t n @ l | p: ptr l):<> void  
  = "linbitvec_bitvec_free"
// end of [bitvec_free]

(* ****** ****** *)

extern fun bitvec_get_at
  {n,i:nat | i < n} (vec: &bitvec_t n, i: size_t i):<> bit
  = "linbitvec_bitvec_get_at"
// end of [bitvec_get_at]

extern fun bitvec_set_at
  {n,i:nat | i < n} (vec: &bitvec_t n, i: size_t i, b: bit):<> void
  = "linbitvec_bitvec_set_at"
// end of [bitvec_set_at]

overload [] with bitvec_get_at
overload [] with bitvec_set_at

(* ****** ****** *)

extern fun bitvec_is_empty {n:nat}
  (vec: &bitvec_t n, n: size_t n): bool
  = "linbitvec_bitvec_is_empty"

extern fun bitvec_isnot_empty {n:nat}
  (vec: &bitvec_t n, n: size_t n): bool

implement bitvec_isnot_empty (vec, n) = ~bitvec_is_empty (vec, n)

(* ****** ****** *)

extern fun bitvec_is_full {n:nat}
  (vec: &bitvec_t n, n: size_t n): bool
  = "linbitvec_bitvec_is_full"

extern fun bitvec_isnot_full {n:nat}
  (vec: &bitvec_t n, n: size_t n): bool

implement bitvec_isnot_full (vec, n) = ~bitvec_is_full (vec, n)

(* ****** ****** *)

// vec1 = vec2 ?
extern fun bitvec_equal {n:nat}
  (vec1: &bitvec_t n, vec2: &bitvec_t n, n: size_t n):<> bool
  = "linbitvec_bitvec_equal"
// end of [bitvec_equal]

extern fun bitvec_notequal {n:nat}
  (vec1: &bitvec_t n, vec2: &bitvec_t n, n: size_t n):<> bool

implement bitvec_notequal (vec1, vec2, n) = ~bitvec_equal (vec1, vec2, n)

(* ****** ****** *)

// vec1 <- vec2
extern fun bitvec_copy {n:nat}
  (vec1: &bitvec_t n, vec2: &bitvec_t n, n: size_t n):<> void
  = "linbitvec_bitvec_copy"
// end of [bitvec_copy]

(* ****** ****** *)

// complement operation
extern fun bitvec_neg {n:nat}
  (vec: &bitvec_t n, n: size_t n): void
  = "linbitvec_bitvec_neg"

extern fun bitvec_or {n:nat}
  (vec1: &bitvec_t n, vec2: &bitvec_t n, n: size_t n): void
  = "linbitvec_bitvec_or"

extern fun bitvec_and {n:nat}
  (vec1: &bitvec_t n, vec2: &bitvec_t n, n: size_t n): void
  = "linbitvec_bitvec_and"

extern fun bitvec_xor {n:nat}
  (vec1: &bitvec_t n, vec2: &bitvec_t n, n: size_t n): void
  = "linbitvec_bitvec_xor"

extern fun bitvec_diff {n:nat}
  (vec1: &bitvec_t n, vec2: &bitvec_t n, n: size_t n): void
  = "linbitvec_bitvec_diff"

(* ****** ****** *)

%{^

#define NBIT_PER_BYTE 8
#define NBIT_PER_BYTE_LOG 3

/* ****** ****** */

#ifndef __WORDSIZE
#error "[__WORDSIZE] is undefined.\n"
#endif

#if (__WORDSIZE == 32)

#define NBYTE_PER_WORD 4
#define NBYTE_PER_WORD_LOG 2
#if (NBYTE_PER_WORD != (1 << NBYTE_PER_WORD_LOG))
#error "NBYTE_PER_WORD != (1 << NBYTE_PER_WORD_LOG)\n"
#endif

#elif (__WORDSIZE == 64)

#define NBYTE_PER_WORD 8
#define NBYTE_PER_WORD_LOG 3
#if (NBYTE_PER_WORD != (1 << NBYTE_PER_WORD_LOG))
#error "NBYTE_PER_WORD != (1 << NBYTE_PER_WORD_LOG)\n"
#endif

#else
#error "[__WORDSIZE] is not supported.\n"
#endif

/* ****** ****** */

#define NBIT_PER_WORD (NBIT_PER_BYTE * NBYTE_PER_WORD)
#define NBIT_PER_WORD_LOG (NBIT_PER_BYTE_LOG + NBYTE_PER_WORD_LOG)
#if (NBIT_PER_WORD != (1 << NBIT_PER_WORD_LOG))
#error "NBIT_PER_WORD != (1 << NBIT_PER_WORD_LOG)\n"
#endif

%}

(* ****** ****** *)

%{^

ats_ptr_type
linbitvec_bitvec_make
  (ats_size_type nbit) {
  uintptr_t *p_vec ; size_t nwrd ;
  nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  p_vec = ATS_CALLOC (nwrd, NBYTE_PER_WORD) ; // initialized to zero
  return p_vec ;
} /* end of [linbitvec_bitvec_make] */

ats_ptr_type // same as [linbitvec_bitvec_make]
linbitvec_bitvec_make_empty (ats_size_type nbit) {
  uintptr_t *p_vec ; size_t nwrd ;
  nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  p_vec = ATS_CALLOC (nwrd, NBYTE_PER_WORD) ; // initialized to zero
  return p_vec ;
} /* end of [linbitvec_bitvec_make_empty] */

ats_ptr_type
linbitvec_bitvec_make_full (ats_size_type nbit) {
  uintptr_t *p_vec, zc; size_t nwrd ; int next ;
  nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  next = (nwrd << NBIT_PER_WORD_LOG) - nbit ; // extra bits
  p_vec = ATS_CALLOC (nwrd, NBYTE_PER_WORD) ; // initialized to zero
  memset (p_vec, 0xFF, nwrd * NBYTE_PER_WORD) ;
/*
** extra bits, which are in the front, must be set to zero!!!
*/
  if (nwrd > 0) { zc = ~0; p_vec[nwrd-1] &= (zc >> next) ; }
  return p_vec ;
} /* end of [linbitvec_bitvec_make_full] */

ats_void_type
linbitvec_bitvec_free
  (ats_ptr_type p_vec) { ATS_FREE (p_vec) ; return ; }
/* end of [linbitvec_bitvec_free] */

%}

(* ****** ****** *)

%{^

ats_bool_type
linbitvec_bitvec_is_empty (
  ats_ptr_type p0, ats_size_type nbit
) {
  int nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  uintptr_t *p = p0 ;
  if (!nwrd) return ats_true_bool ;
  if (*p != 0) return ats_false_bool ;
  while (--nwrd > 0) { if (*++p != 0) return ats_false_bool ; }
  return ats_true_bool ;
} /* end of [linbitvec_bitvec_is_empty] */

ats_bool_type
linbitvec_bitvec_is_full (
  ats_ptr_type p0, ats_size_type nbit
) {
  int nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  int next = (nwrd << NBIT_PER_WORD_LOG) - nbit ; // extra bits
  uintptr_t *p = p0, zc = ~0 ;
  while (nwrd > 1) {
    if (*p != zc) return ats_false_bool ; --nwrd ; ++p ;
  } ;
/*
** extra bits, which are in the front, must be zero!!!
*/
  if (nwrd) { if (*p != (zc >> next)) return ats_false_bool ; } ;
  return ats_true_bool ;  
} /* end of [linbitvec_bitvec_is_full] */

%}

(* ****** ****** *)

%{^

ats_bool_type
linbitvec_bitvec_equal (
  ats_ptr_type p10, ats_ptr_type p20, ats_size_type nbit
) {
  int nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  uintptr_t *p1 = p10, *p2 = p20 ;
  if (!nwrd) return ats_true_bool ;
  if (*p1 != *p2) return ats_false_bool ;
  while (--nwrd > 0) { if (*++p1 != *++p2) return ats_false_bool ; } ;
  return ats_true_bool ;  
} /* end of [linbitvec_bitvec_copy] */

%}

(* ****** ****** *)

%{^

ats_void_type
linbitvec_bitvec_copy (
  ats_ptr_type p10, ats_ptr_type p20, ats_size_type nbit
) {
  int nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  uintptr_t *p1 = p10, *p2 = p20 ;
  if (!nwrd) return ;
  *p1 = *p2 ; while (--nwrd > 0) { *(++p1) = *(++p2) ; }
  return ;  
} /* end of [linbitvec_bitvec_copy] */

%}

(* ****** ****** *)

%{^

ats_void_type
linbitvec_bitvec_neg (
  ats_ptr_type p0, ats_size_type nbit
) {
  int nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  int next = (nwrd << NBIT_PER_WORD_LOG) - nbit ; // extra bits
  uintptr_t *p = p0, zc = ~0 ;
  while (nwrd > 1) {
    *p = ~(*p) ; --nwrd ; ++p ;
  }
/*
** extra bits, which are in the front, must be set to zero!!!
*/
  if (nwrd > 0) { *p = ~(*p) ; *p &= (zc >> next) ; }
  return ;  
} /* end of [linbitvec_bitvec_neg] */

ats_void_type
linbitvec_bitvec_or (
  ats_ptr_type p10, ats_ptr_type p20, ats_size_type nbit
) {
  int nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  uintptr_t *p1 = p10, *p2 = p20 ;
  if (!nwrd) return ;
  *p1 |= *p2 ; while (--nwrd > 0) { *(++p1) |= *(++p2) ; }
  return ;  
} /* end of [linbitvec_bitvec_or] */

ats_void_type
linbitvec_bitvec_and (
  ats_ptr_type p10, ats_ptr_type p20, ats_size_type nbit
) {
  int nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  uintptr_t *p1 = p10, *p2 = p20 ;
  if (!nwrd) return ;
  *p1 &= *p2 ; while (--nwrd > 0) { *(++p1) &= *(++p2) ; }
  return ;  
} /* end of [linbitvec_bitvec_and] */

ats_void_type
linbitvec_bitvec_xor ( // symmetric difference
  ats_ptr_type p10, ats_ptr_type p20, ats_size_type nbit
) {
  int nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  uintptr_t *p1 = p10, *p2 = p20 ;
  if (!nwrd) return ;
  *p1 ^= *p2 ; while (--nwrd > 0) { *(++p1) ^= *(++p2) ; }
  return ;  
} /* end of [linbitvec_bitvec_xor] */

ats_void_type
linbitvec_bitvec_diff ( // difference
  ats_ptr_type p10, ats_ptr_type p20, ats_size_type nbit
) {
  int nwrd = (nbit + NBIT_PER_WORD - 1) >> NBIT_PER_WORD_LOG ;
  uintptr_t *p1 = p10, *p2 = p20 ;
  if (!nwrd) return ;
  *p1 &= ~(*p2) ; while (--nwrd > 0) { *(++p1) &= ~(*(++p2)) ; }
  return ;  
} /* end of [linbitvec_bitvec_diff] */

%}

(* ****** ****** *)

(* end of [linbitvec.dats] *)
