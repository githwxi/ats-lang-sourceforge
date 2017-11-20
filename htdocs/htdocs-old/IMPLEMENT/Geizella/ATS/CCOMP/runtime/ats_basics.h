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

#ifndef __ATS_BASICS_H
#define __ATS_BASICS_H

#ifdef __ATS_INLINE_PRIMITIVES
#define ATSprimitive static inline
#else
#define ATSprimitive
#endif /* __ATS_INLINE_PRIMITIVES */

#define ATSexport

#define ATSstringize(id) # id
#define ATSunused __attribute__ ((unused))

/* ****** ****** */

#define ATSextern(ty, var) extern ty var
#define ATSstatic(ty, var) static ty var
#define ATSstatic_void(var)
#define ATSlocal(ty, var) ty ATSunused var
#define ATSlocal_void(var)
#define ATSglobal(ty, var) ty var

/* ****** ****** */

#define ATSdeadcode() \
  do { \
    fprintf ( \
      stderr, \
      "Error in the file %s on line %d: the deadcode is executed!\n", \
      __FILE__, __LINE__ \
    ); \
    abort (); \
  } while (0);

/* boolean values */
#define ats_true_bool 1
#define ats_false_bool 0

/* while loop */
#define ats_while_begin(clab) \
while(ats_true_bool) { \
clab:

#define ats_while_end(blab,clab) \
goto clab ; \
blab: break ; \
}

/* closure function selection */
#define ats_closure_fun(f) ((ats_clo_ptr_type)f)->closure_fun

/* ****** ****** */

typedef void *parallel_spawn_thunk_t ;
typedef void *parallel_sync_token_t ;
extern parallel_sync_token_t atslib_parallel_spawn (parallel_spawn_thunk_t) ;
extern void  atslib_parallel_sync (parallel_sync_token_t) ;

/* ****** ****** */

#endif /* __ATS_BASICS_H */

/* end of [ats_basics.h] */
