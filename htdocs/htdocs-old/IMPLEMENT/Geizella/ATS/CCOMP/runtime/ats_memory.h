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

/* ****** ****** */

#ifndef	__ATS_MEMORY_H
#define __ATS_MEMORY_H

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

extern ats_ptr_type ats_malloc_ngc (const ats_int_type n) ;

extern ats_ptr_type
ats_calloc_ngc (const ats_int_type n, const ats_int_type sz) ;

extern ats_void_type ats_free_ngc (const ats_ptr_type p) ;

extern ats_ptr_type
ats_realloc_ngc (const ats_ptr_type p, const ats_int_type n) ;

/* ****** ****** */

extern ats_void_type ats_gc_init () ;
extern ats_void_type ats_gc_mark_root (ats_ptr_type) ;

/* ****** ****** */

extern ats_ptr_type ats_malloc_gc (const ats_int_type n) ;

extern ats_ptr_type
ats_calloc_gc (const ats_int_type n, const ats_int_type sz) ;

extern ats_void_type ats_free_gc (const ats_ptr_type p) ;

extern ats_ptr_type
ats_realloc_gc (const ats_ptr_type p, const ats_int_type n) ;

/* ****** ****** */

#endif	/* __ATS_MEMORY_H */

/* end of [ats_memory.h] */

