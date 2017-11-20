/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi.
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 */

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef __BYTE_CATS
#define __BYTE_CATS

/* ****** ****** */

#include <ctype.h>
#include <stdio.h>

/* ****** ****** */

#include "ats_memory.h"
#include "ats_types.h"

/* ****** ****** */

static inline
ats_byte_type
atspre_byte_of_char (ats_char_type c) { return c ; }

static inline
ats_char_type
atspre_char_of_byte (ats_byte_type b) { return b ; }

static inline
ats_byte_type
atspre_byte_of_int (ats_int_type i) { return i ; }

static inline
ats_int_type
atspre_int_of_byte (ats_byte_type b) { return b ; }

/* ****** ****** */

// arithmetic operations

static inline
ats_byte_type
atspre_succ_byte(ats_byte_type i) { return (i + 1) ; }

static inline
ats_byte_type
atspre_pred_byte(ats_byte_type i) { return (i - 1) ; }

static inline
ats_byte_type
atspre_add_byte_byte(ats_byte_type i1, ats_byte_type i2) {
  return (i1 + i2) ;
}

static inline
ats_byte_type
atspre_sub_byte_byte(ats_byte_type i1, ats_byte_type i2) {
  return (i1 - i2) ;
}

static inline
ats_byte_type
atspre_mul_byte_byte(ats_byte_type i1, ats_byte_type i2) {
  return (i1 * i2) ;
}

static inline
ats_byte_type
atspre_div_byte_byte(ats_byte_type i1, ats_byte_type i2) {
  return (i1 / i2) ;
}

/* ****** ****** */

static inline
ats_bool_type
atspre_lt_byte_byte(ats_byte_type b1, ats_byte_type b2) {
  return (b1 < b2) ;
}

static inline
ats_bool_type
atspre_lte_byte_byte(ats_byte_type b1, ats_byte_type b2) {
  return (b1 <= b2) ;
}

static inline
ats_bool_type
atspre_gt_byte_byte(ats_byte_type b1, ats_byte_type b2) {
  return (b1 > b2) ;
}

static inline
ats_bool_type
atspre_gte_byte_byte(ats_byte_type b1, ats_byte_type b2) {
  return (b1 >= b2) ;
}

static inline
ats_bool_type
atspre_eq_byte_byte(ats_byte_type b1, ats_byte_type b2) {
  return (b1 == b2) ;
}

static inline
ats_bool_type
atspre_neq_byte_byte(ats_byte_type b1, ats_byte_type b2) {
  return (b1 != b2) ;
}

// bitwise operations

static inline
ats_byte_type
atspre_lnot_byte(ats_byte_type b) { return (~b) ; }

static inline
ats_byte_type
atspre_land_byte_byte(ats_byte_type b1, ats_byte_type b2) {
  return (b1 & b2) ;
}

static inline
ats_byte_type
atspre_lor_byte_byte(ats_byte_type b1, ats_byte_type b2) {
  return (b1 | b2) ;
}

static inline
ats_byte_type
atspre_lxor_byte_byte(ats_byte_type b1, ats_byte_type b2) {
  return (b1 ^ b2) ;
}

static inline
ats_byte_type
atspre_lsl_byte_int1(ats_byte_type b, ats_int_type n) {
  return (b << n) ;
}

static inline
ats_byte_type
atspre_lsr_byte_int1(ats_byte_type b, ats_int_type n) {
  return (b >> n) ;
}

// print functions

static inline
ats_void_type
atspre_fprint_byte (const ats_ptr_type out, const ats_byte_type b) {
  int n = fputc (b, (FILE *)out) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_byte] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_byte(const ats_byte_type c) {
  atspre_stdout_view_get () ;
  atspre_fprint_byte(stdout, c) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_byte(const ats_byte_type c) {
  atspre_stderr_view_get () ;
  atspre_fprint_byte(stderr, c) ;
  atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

#define atspre_lt_byte1_byte1 atspre_lt_byte_byte
#define atspre_lte_byte1_byte1 atspre_lte_byte_byte
#define atspre_gt_byte1_byte1 atspre_gt_byte_byte
#define atspre_gte_byte1_byte1 atspre_gte_byte_byte
#define atspre_eq_byte1_byte1 atspre_eq_byte_byte
#define atspre_neq_byte1_byte1 atspre_neq_byte_byte

/* ****** ****** */

#endif /* __BYTE_CATS */

/* end of [byte.cats] */
