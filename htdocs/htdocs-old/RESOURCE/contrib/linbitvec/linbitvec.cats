/*
**
** An implementation of functional maps based on AVL trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: May, 2009
**
*/

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

/* ****** ****** */

#ifndef ATS_CONTRIB_LINBITVEC_CATS
#define ATS_CONTRIB_LINBITVEC_CATS

/* ****** ****** */

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

//
// these functions need to be inlined for efficiency!
//

/* ****** ****** */

static inline
ats_int_type
linbitvec_bitvec_get_at
  (ats_ptr_type p_vec, ats_size_type i) {
  size_t q, r ;
  q = i >> NBIT_PER_WORD_LOG ; r = i & (NBIT_PER_WORD - 1) ;
  return (((uintptr_t*)p_vec)[q] >> r) & 0x1 ;
} /* end of [linbitvec_bitvec_get_at] */

static inline
ats_void_type
linbitvec_bitvec_set_at
  (ats_ptr_type p_vec, ats_size_type i, ats_int_type b) {
  size_t q, r ;
  q = i >> NBIT_PER_WORD_LOG ; r = i & (NBIT_PER_WORD - 1) ;
  if (b) {
    ((uintptr_t*)p_vec)[q] |= (1 << r) ;
  } else {
    ((uintptr_t*)p_vec)[q] &= ~(1 << r) ;
  } ;
  return ;
} /* end of [linbitvec_bitvec_set_at] */

/* ****** ****** */

#endif // end of [#ifndef ATS_CONTRIB_LINBITVEC_CATS]

/* ****** ****** */

/* end of [linbitvec.cats] */
