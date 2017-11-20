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

#ifndef __BOOL_CATS
#define __BOOL_CATS

/* ****** ****** */

#include <stdio.h>
#include "ats_types.h"

/* ****** ****** */

static inline
ats_bool_type
atspre_bool1_of_bool(const ats_bool_type b) { return b ; }

/* ****** ****** */

static inline
ats_bool_type
atspre_neg_bool(const ats_bool_type b) {
  return (b ? ats_false_bool : ats_true_bool) ;
}

/* ****** ****** */

static inline
ats_bool_type
atspre_add_bool_bool
  (const ats_bool_type b1, const ats_bool_type b2) {
  if (b1) { return ats_true_bool ; } else { return b2 ; }
}

static inline
ats_bool_type
atspre_mul_bool_bool
  (const ats_bool_type b1, const ats_bool_type b2) {
  if (b1) { return b2 ; } else { return ats_false_bool ; }
}

/* ****** ****** */

static inline
ats_bool_type
atspre_lt_bool_bool
  (const ats_bool_type b1, const ats_bool_type b2) {
  return (!b1 && b2) ;
}

static inline
ats_bool_type
atspre_lte_bool_bool
  (const ats_bool_type b1, const ats_bool_type b2) {
  return (!b1 || b2) ;
}

static inline
ats_bool_type
atspre_gt_bool_bool
  (const ats_bool_type b1, const ats_bool_type b2) {
  return (b1 && !b2) ;
}

static inline
ats_bool_type
atspre_gte_bool_bool
  (const ats_bool_type b1, const ats_bool_type b2) {
  return (b1 || !b2) ;
}

static inline
ats_bool_type
atspre_eq_bool_bool
  (const ats_bool_type b1, const ats_bool_type b2) {
  if (b1) { return b2 ; } else { return !b2 ; }
}

static inline
ats_bool_type
atspre_neq_bool_bool
  (const ats_bool_type b1, const ats_bool_type b2) {
  if (b1) { return !b2 ; } else { return b2 ; }
}

// print functions

static inline
ats_void_type
atspre_fprint_bool (const ats_ptr_type out, const ats_bool_type b) {
  int n ;

  if (b) {
    n = fprintf ((FILE *)out, "true") ;
  } else {
    n = fprintf ((FILE *)out, "false") ;
  }

  if (n < 0) {
    ats_exit_errmsg(n, "Exit: [fprint_bool] failed.\n") ;
  }

  return ;
}

static inline
ats_void_type
atspre_print_bool(const ats_bool_type b) {
  atspre_stdout_view_get() ;
  atspre_fprint_bool (stdout, b) ;
  atspre_stdout_view_set() ;
  return ;
}

static inline
ats_void_type
atspre_prerr_bool(const ats_bool_type b) {
  atspre_stderr_view_get() ;
  atspre_fprint_bool (stderr, b) ;
  atspre_stderr_view_set() ;
  return ;
}

// stringization

static inline
ats_ptr_type
atspre_tostring_bool(const ats_bool_type b) {
  return (b ? "true" : "false") ;
}

/* ****** ****** */

#define atspre_neg_bool1 atspre_neg_bool
#define atspre_add_bool1_bool1 atspre_add_bool_bool
#define atspre_mul_bool1_bool1 atspre_mul_bool1_bool1

#define atspre_lt_bool1_bool1 atspre_lt_bool_bool
#define atspre_lte_bool1_bool1 atspre_lte_bool_bool
#define atspre_gt_bool1_bool1 atspre_gt_bool_bool
#define atspre_gte_bool1_bool1 atspre_gte_bool_bool
#define atspre_eq_bool1_bool1 atspre_eq_bool_bool
#define atspre_neq_bool1_bool1 atspre_neq_bool_bool

/* ****** ****** */

#endif /* __BOOL_CATS */

/* end of [bool.cats] */
