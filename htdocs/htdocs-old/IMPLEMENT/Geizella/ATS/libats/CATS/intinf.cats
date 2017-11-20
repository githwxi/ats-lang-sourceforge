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
 * ATS is  free software;  you can redistribute it and/or modify it under
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
 * Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
 * 02110-1301, USA.
 *
 */

/*
 *
 * Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) 
 *
 */

#ifndef _LIBATS_INTINF_CATS
#define _LIBATS_INTINF_CATS

/* ****** ****** */

static inline
ats_bool_type
atslib_lt_intinf_int (ats_ptr_type i, ats_int_type j) {
  return (atslib_mpz_cmp_int (i, j) < 0) ;
}

static inline
ats_bool_type
atslib_lte_intinf_int (ats_ptr_type i, ats_int_type j) {
  return (atslib_mpz_cmp_int (i, j) <= 0) ;
}

/* ****** ****** */

static inline
ats_bool_type
atslib_gt_intinf_int (ats_ptr_type i, ats_int_type j) {
  return (atslib_mpz_cmp_int (i, j) > 0) ;
}

static inline
ats_bool_type
atslib_gte_intinf_int (ats_ptr_type i, ats_int_type j) {
  return (atslib_mpz_cmp_int (i, j) >= 0) ;
}

/* ****** ****** */

static inline
ats_bool_type
atslib_eq_intinf_int (ats_ptr_type i, ats_int_type j) {
  return (atslib_mpz_cmp_int (i, j) == 0) ;
}

static inline
ats_bool_type
atslib_neq_intinf_int (ats_ptr_type i, ats_int_type j) {
  return (atslib_mpz_cmp_int (i, j) != 0) ;
}

/* ****** ****** */

#endif /* _LIBATS_INTINF_CATS */

/* end of [intinf.cats] */ 
