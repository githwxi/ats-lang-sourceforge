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

#ifndef __REFERENCE_CATS
#define __REFERENCE_CATS

/* ****** ****** */

#include <string.h> // for [memcpy]

/* ****** ****** */

#include "ats_memory.h"
#include "ats_types.h"

/* ****** ****** */

static inline
ats_ptr_type
atspre_ref_make_elt_tsz (ats_ptr_type p0, ats_int_type sz) {
  ats_ptr_type p ;
  p = ats_malloc_gc (sz) ;
  memcpy (p, p0, sz) ;
  return p ;
}

static inline
ats_ptr_type
atspre_ref_void_make () { return (ats_ptr_type)0 ; }

static inline
ats_ptr_type
atspre_ref_make_view_ptr (ats_ptr_type p) { return p ; }

static inline
ats_ptr_type
atspre_ref_get_view_ptr (ats_ptr_type r) { return r ; }

/* ****** ****** */

#endif /* __REFERENCE_CATS */

/* end of [reference.cats] */
