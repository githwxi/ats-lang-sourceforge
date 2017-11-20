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
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 */

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef _LIBC_COMPLEX_CATS
#define _LIBC_COMPLEX_CATS

/* ****** ****** */

#include <complex.h>
#include <math.h>
#include <stdio.h> // for [stdout]

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

typedef double complex ats_complex_type ;
typedef float complex ats_fcomplex_type ;
typedef long double complex ats_lcomplex_type ;

/* ****** ****** */

static inline
ats_complex_type
atslib_complex_of_int (ats_int_type i) {
  return i;
}

static inline
ats_complex_type
atslib_complex_of_double (ats_double_type f) {
  return f;
}

static inline
ats_complex_type
atslib_complex_make_cart (ats_double_type r, ats_double_type i) {
  return (r + i * I) ;
}

static inline
ats_complex_type
atslib_complex_make_polar (ats_double_type r, ats_double_type t) {
  return (r * cos(t)) + (r * sin(t)) * I ;
}

/* ****** ****** */

static inline
ats_complex_type
atslib_conj_complex (ats_complex_type z) { return conj(z) ; }

static inline
ats_complex_type
atslib_sqrt_complex (ats_complex_type z) { return csqrt(z) ; }

static inline
ats_complex_type
atslib_exp_complex (ats_complex_type z) { return cexp(z) ; }

/* ****** ****** */

extern
ats_void_type
atslib_fprint_complex (ats_ptr_type file, ats_complex_type z) ;

static inline
ats_void_type
atslib_print_complex (ats_complex_type f) {
  atspre_stdout_view_get () ;
  atslib_fprint_complex (stdout, f) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atslib_prerr_complex (ats_complex_type f) {
  atspre_stderr_view_get () ;
  atslib_fprint_complex (stderr, f) ;
  atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

#endif /* _LIBC_COMPLEX_CATS */

/* end of [complex.cats] */
