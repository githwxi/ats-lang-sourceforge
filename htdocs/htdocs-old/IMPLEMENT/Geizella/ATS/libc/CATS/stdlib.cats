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

#ifndef _LIBC_STDLIB_CATS
#define _LIBC_STDLIB_CATS

/* ****** ****** */

#include <stdlib.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

static inline
ats_double_type
atslib_atof(const ats_ptr_type s) { return atof(s) ; }

static inline
ats_int_type
atslib_atoi(const ats_ptr_type s) { return atoi(s) ; }

static inline
ats_lint_type
atslib_atol (const ats_ptr_type s) { return atol(s) ; }

static inline
ats_llint_type
atslib_atoll (const ats_ptr_type s) { return atoll(s) ; }

//

static inline
ats_ptr_type
atslib_getenv (const ats_ptr_type name) {
  char *res = getenv(name) ;
  if (!name) {
    atspre_exit_prerrf (1, "Exit: [getenv(%s)] failed.\n", name) ;
  }
  return res ;
}

static inline
ats_ptr_type
atslib_getenv_opt (ats_ptr_type name) {
  return getenv(name) ;
}

//

static inline
ats_int_type
atslib_bsearch
  (ats_ref_type key,
   ats_ptr_type base,
   ats_int_type nmemb,
   ats_int_type size,
   ats_fun_ptr_type compar)
{
  void *p ;
  p = bsearch((void *)key, (void *)base, (size_t)nmemb, (size_t)size, (int(*)(const void*, const void*))compar) ;
  if (!p) return -1 ;
  return ((char *)p - (char *)base) / size ;
}

static inline
ats_void_type
atslib_qsort
  (ats_ptr_type base,
   ats_int_type nmemb,
   ats_int_type size,
   ats_fun_ptr_type compar)
{
  qsort((void *)base, (size_t)nmemb, (size_t)size, (int(*)(const void*, const void*))compar) ;
  return ;
}

/* ****** ****** */

#endif /* _LIBC_STDLIB_CATS */

/* end of [stdlib.cats] */
