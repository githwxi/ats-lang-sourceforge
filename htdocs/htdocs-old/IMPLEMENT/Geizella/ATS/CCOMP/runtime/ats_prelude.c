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

#include <stdarg.h>
#include <stdlib.h>
#include <stdio.h>

/* ****** ****** */

#include "ats_exception.h"
#include "ats_memory.h"
#include "ats_types.h"

/* ****** ****** */

// The following variables are used in basics.dats
int ats_stdin_view_lock = 1 ;
int ats_stdout_view_lock = 1 ;
int ats_stderr_view_lock = 1 ;

/* ****** ****** */

// some common exceptions

ats_exn_type AssertionExceptionCon = { 10, "AssertionException" } ;
ats_exn_ptr_type AssertionException = &AssertionExceptionCon ;

ats_exn_type DivisionByZeroExceptionCon = { 20, "DivisionByZeroException" } ;
ats_exn_ptr_type DivisionByZeroException = &DivisionByZeroExceptionCon ;

ats_exn_type NotFoundExceptionCon = { 30, "NotFoundException" } ;
ats_exn_ptr_type NotFoundException = &NotFoundExceptionCon ;

ats_exn_type OverflowExceptionCon = { 40, "OverflowException" } ;
ats_exn_ptr_type OverflowException = &OverflowExceptionCon ;

ats_exn_type SubscriptExceptionCon = { 50, "SubscriptException" } ;
ats_exn_ptr_type SubscriptException = &SubscriptExceptionCon ;

/* ****** ****** */

/* tags for exception constructors */

// numbers less than 1000 are reserved
int ats_exception_con_tag = 1000 ;

#ifdef ATS_MULTITHREAD
__thread
ats_exception_frame_type *ats_exception_stack = NULL ;
#else
ats_exception_frame_type *ats_exception_stack = NULL ;
#endif

/* function for handling uncaught exceptions */

ats_void_type
ats_handle_exception (const ats_exn_ptr_type exn) {
  fprintf(stderr, "Uncaught exception: %s(%d)\n", exn->name, exn->tag);
  exit(1);
}

/* functions for handling match failures */

ats_void_type
ats_match_failure (void) {
  ats_exit_errmsg(1, "Exit: match failure.\n") ;
  return ;
}

ats_void_type
ats_funarg_match_failure (void) {
  ats_exit_errmsg(1, "Exit: funarg match failure.\n") ;
  return ;
}

/* ****** ****** */

/* function for memory allocation and deallocation */

#ifdef __ATS_GC // generic GC for ATS
#include "GC/include/gc.h"
#elif __ATS_gcats // special GC for ATS
#include "gcats/gc.h"
#elif __ATS_gc // special GC for ATS
#include "gc/gc.h"
#else // no GC for ATS
#include <stdlib.h>
#endif

/* ****** ****** */

ats_ptr_type
ats_malloc_ngc (const ats_int_type n) {
  void *p ;
#ifdef __ATS_GC
  p = GC_malloc(n) ;
#elif __ATS_gcats
  /*
  fprintf (stdout, "ats_malloc_ngc: _ATS_gcats: n = %i\n", n) ;
  */
  p = gcats0_malloc(n) ;
  /*
  fprintf (stdout, "ats_malloc_ngc: _ATS_gcats: p = %p(%i)\n", p, p) ;
  */
#elif __ATS_gc
  /*
  fprintf (stdout, "ats_malloc_ngc: _ATS_gc: n = %i\n", n) ;
  */
  p = gc_allocate_persistant_byte(n) ;
  /*
  fprintf (stdout, "ats_malloc_ngc: _ATS_gc: p = %p(%i)\n", p, p) ;
  */
#else
  p = malloc(n) ;
#endif
  if (!p) ats_exit_errmsg(1, "Exit: [malloc] failed.\n") ;
  return p ;
}

ats_ptr_type
ats_calloc_ngc (const ats_int_type n, const ats_int_type sz)
{
  void *p ;
#ifdef __ATS_GC
  p = GC_malloc(n * sz) ;
#elif __ATS_gcats
  /*
  fprintf (stdout, "ats_calloc: _ATS_gcats: n = %i and sz = %i\n", n, sz) ;
  */
  p = gcats0_calloc(n, sz) ;
#elif __ATS_gc
  /*
  fprintf (stdout, "ats_calloc: _ATS_gc: n = %i and sz = %i\n", n, sz) ;
  */
  p = gc_allocate_persistant_byte(n * sz) ;
#else
  p = calloc(n, sz) ;
#endif
  if (!p) ats_exit_errmsg(1, "Exit: [calloc] failed.\n") ;
  return p ;
}

ats_void_type
ats_free_ngc (const ats_ptr_type p) {
#ifdef __ATS_GC
  GC_free(p) ; return ;
#elif __ATS_gcats
  /*
  fprintf (stdout, "ats_free_ngc: _ATS_gcats: p = %p\n", p) ;
  */
  gcats0_free(p) ;
#elif __ATS_gc
  /*
  fprintf (stdout, "ats_free_ngc: _ATS_gc: p = %p\n", p) ;
  */
  gc_free_persistant(p) ; return ;
#else
  free(p) ; return ;
#endif

}

ats_ptr_type
ats_realloc_ngc (const ats_ptr_type p, const ats_int_type n) {
  void *p_new ;
#ifdef __ATS_GC
  p_new = GC_realloc(p, n) ;
#elif __ATS_gcats
  p_new = gcats0_realloc(p, n) ;
#elif __ATS_gc
  p_new = gc_reallocate_persistant_byte(p, n) ;
#else
  p_new = realloc(p, n) ;
#endif
  if (!p_new) ats_exit_errmsg(1, "Exit: [realloc] failed.\n") ;
  return p_new ;
}

/* memory allocation/deallocation with GC support */

ats_void_type ats_gc_init () {

#ifdef __ATS_GC
  GC_init () ; return ;
#elif __ATS_gcats
  gcats_init () ; return ;
#elif __ATS_gc
  gc_init () ; return ;
#endif

}

ats_void_type
ats_gc_markroot (const ats_ptr_type p, const size_t sz) {
#ifdef __ATS_GC
#elif __ATS_gcats
  /*
  fprintf (stdout, "ats_gc_markroot: p = %p and sz = %i\n", p, sz) ;
  */
  gcats_markroot(p, sz) ;
#elif __ATS_gc
  /*
  fprintf (stdout, "ats_gc_markroot: p = %p and sz = %i\n", p, sz) ;
  */
  gc_markroot(p, sz) ;
#else
#endif
  return ;
}

ats_ptr_type
ats_malloc_gc (const ats_int_type n) {
  void *p ;
#ifdef __ATS_GC
  p = GC_malloc(n) ;
#elif __ATS_gcats
  /*
  fprintf (stdout, "ats_malloc_gc: _ATS_gcats: n = %i\n", n) ;
  */
  p = gcats1_malloc(n) ;
  /*
  fprintf (stdout, "ats_malloc_gc: _ATS_gcats: p = %p(%i)\n", p, p) ;
  */
#elif __ATS_gc
  /*
  fprintf (stdout, "ats_malloc_gc: _ATS_gc: n = %i\n", n) ;
  */
  p = gc_alloc_byte(n) ;
  /*
  fprintf (stdout, "ats_malloc_gc: _ATS_gc: p = %p(%i)\n", p, p) ;
  */
#else
  p = malloc(n) ;
#endif
  if (!p) ats_exit_errmsg(1, "Exit: [malloc_gc] failed.\n") ;
  return p ;
}

ats_ptr_type
ats_calloc_gc (const ats_int_type n, const ats_int_type sz) {
  void *p ;
#ifdef __ATS_GC
  p = GC_malloc(n*sz) ;
#elif __ATS_gcats
  /*
  fprintf (stdout, "ats_calloc_gc: _ATS_gcats: n = %i and sz = %i\n", n, sz) ;
  */
  p = gcats1_calloc(n, sz) ;
#elif __ATS_gc
  /*
  fprintf (stdout, "ats_calloc_gc: _ATS_gc: n = %i and sz = %i\n", n, sz) ;
  */
  p = gc_alloc_byte_zero(n*sz) ;
#else
  p = calloc(n, sz) ;
#endif
  if (!p) ats_exit_errmsg(1, "Exit: [malloc_gc] failed.\n") ;
  return p ;
}

ats_void_type
ats_free_gc (const ats_ptr_type p) {
#ifdef __ATS_GC
  GC_free(p) ;
#elif __ATS_gcats
  /*
  fprintf (stdout, "ats_free_gc: _ATS_gcats: p = %p\n", p) ;
  */
  gcats1_free(p) ;
#elif __ATS_gc
  /*
  fprintf (stdout, "ats_free_gc: _ATS_gc: p = %p\n", p) ;
  */
  gc_free(p) ;
#else
  free(p) ;
#endif
  return ;
}

/* ****** ****** */

#ifdef ATS_MULTITHREAD

static
ats_ptr_type ats_pthread_app (ats_ptr_type f) {
  ((void (*)(ats_ptr_type))((ats_clo_ptr_type)f)->closure_fun)(f) ;
  ats_free_gc (f) ; // this is a linear application
  return (ats_ptr_type)0 ;
}

#ifdef __ATS_gc
extern int gc_create_pthread (
  void *(*start_routine)(void*), void *arg, pthread_t* pid, int detached
) ;
#endif

ats_void_type
ats_pthread_create_detach (ats_ptr_type thunk) {
#ifdef __ATS_GC
  fprintf (stderr, "There is currently no support for pthreads under this GC (GC).\n");
  exit (1) ;
#elif __ATS_gcats
  fprintf (stderr, "There is currently no support for pthreads under this GC (gcats).\n");
  exit (1) ;
#elif __ATS_gc
  int ret ;
  ret = gc_create_pthread (ats_pthread_app, thunk, NULL, 1/*detached*/) ;
  if (ret != 0) { perror ("ats_pthread_create_detach: ") ; exit(1) ; }
#else
  pthread_t tid ; int ret ;
  ret = pthread_create (&tid, NULL, ats_pthread_app, thunk) ;
  if (ret != 0) { perror ("ats_pthread_create_detach: ") ; exit(1) ; }
#endif
  return ;
} // end of [ats_pthread_create_detach]

static inline
ats_void_type ats_pthread_exit () {
#ifdef __ATS_GC
  fprintf (stderr, "There is currently no support for pthreads under this GC.\n");
  exit (1) ;
#elif __ATS_gcats
  fprintf (stderr, "There is currently no support for pthreads under this GC.\n");
  exit (1) ;
#elif __ATS_gc
  pthread_exit (NULL) ;
#else
  pthread_exit (NULL) ;
#endif
  return ;
} // end of [ats_pthread_exit]

/* ****** ****** */

#endif /* [ATS_MULTITHREAD] */

/* end of [ats_prelude.c] */
