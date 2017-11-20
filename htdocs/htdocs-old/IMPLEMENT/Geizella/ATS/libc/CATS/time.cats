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

#ifndef _LIBC_TIME_CATS
#define _LIBC_TIME_CATS

/* ****** ****** */

#include <time.h>

/* ****** ****** */

#include "ats_types.h"
typedef time_t ats_time_t_type ;
typedef clock_t ats_clock_t_type ;

/* ****** ****** */

static inline
ats_lint_type
atslib_lint_of_time_t (time_t t) { return t ; }

static inline
ats_double_type
atslib_double_of_time_t (time_t t) { return t ; }

static inline
ats_time_t_type
atslib_time_get () { return time((time_t *)0) ; }

static inline
ats_time_t_type
atslib_time_get_and_set (ats_ptr_type p) {
  return time((time_t *)p) ;
}

static inline
ats_double_type
atslib_difftime (time_t finish, time_t start) {
  return difftime(finish, start) ;
}

/* ****** ****** */

static inline
ats_lint_type
atslib_lint_of_clock_t (clock_t t) { return t ; }

static inline
ats_double_type
atslib_double_of_clock_t (clock_t t) { return t ; }

/* ****** ****** */

static inline
ats_clock_t_type
atslib_clock (void) { return clock (); }

/* ****** ****** */

#endif /* _LIBC_TIME_CATS */

/* end of [time.cats] */
