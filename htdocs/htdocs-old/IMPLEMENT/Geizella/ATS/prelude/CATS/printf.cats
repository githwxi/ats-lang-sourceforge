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

#ifndef __PRINTF_CATS
#define __PRINTF_CATS

/* ****** ****** */

#include <stdarg.h>
#include <stdio.h>

/* ****** ****** */

static
ats_int_type
atspre_fprintf_err
  (ats_ptr_type file, ats_ptr_type fmt, ...) {
  int n ;
  va_list ap ;
  va_start(ap, fmt) ;
  n = vfprintf((FILE *)file, (char *)fmt, ap) ;
  va_end(ap) ;
  return n ; 
}

static
ats_void_type
atspre_fprintf(ats_ptr_type file, ats_ptr_type fmt, ...) {
  int n ;
  va_list ap ;
  va_start(ap, fmt) ;
  n = vfprintf((FILE *)file, (char *)fmt, ap) ;
  va_end(ap) ;
  if (n < 0) ats_exit_errmsg(n, "Exit: [fprintf] failed\n") ;
  return ;
}

static
ats_int_type
atspre_printf_err (ats_ptr_type fmt, ...) {
  int n ;
  va_list ap ;
  va_start(ap, fmt) ;
  n = vprintf((char *)fmt, ap) ;
  va_end(ap) ;
  return n ; 
}

static
ats_void_type
atspre_printf(ats_ptr_type fmt, ...) {
  int n ;
  va_list ap ;
  atspre_stdout_view_get() ;
  va_start(ap, fmt) ;
  n = vprintf((char *)fmt, ap) ;
  va_end(ap) ;
  atspre_stdout_view_set() ;
  if (n < 0) ats_exit_errmsg(n, "[printf] failed\n") ;
  return ;
}

static
ats_void_type
atspre_prerrf(ats_ptr_type fmt, ...) {
  int n ;
  va_list ap ;
  atspre_stderr_view_get() ;
  va_start(ap, fmt) ;
  n = vfprintf(stderr, (char *)fmt, ap) ;
  va_end(ap) ;
  atspre_stderr_view_set() ;
  if (n < 0) ats_exit_errmsg(n, "[prerrf] failed\n") ;
  return ;
}

/* ****** ****** */

#endif /* __PRINTF_CATS */

/* end of [printf.cats] */
