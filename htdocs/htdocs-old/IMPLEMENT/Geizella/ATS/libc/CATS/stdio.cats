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

#ifndef _LIBC_STDIO_CATS
#define _LIBC_STDIO_CATS

/* ****** ****** */

#include <errno.h>
#include <stdio.h>

/* ****** ****** */

#include "ats_types.h"

typedef FILE ats_FILE_viewtype ;
typedef fpos_t ats_fpos_t_type ;

/* ****** ****** */

static inline
ats_void_type
atslib_clearerr(ats_ptr_type file) {
  clearerr ((FILE *)file) ; return ;
}

/* ****** ****** */

static inline
ats_int_type
atslib_fclose_err(ats_ptr_type file) {
  return fclose((FILE *)file) ;
}

static inline
ats_void_type
atslib_fclose(ats_ptr_type file) {
  int n = fclose((FILE *)file) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fclose] failed\n") ;
  }
  return ;
}

static inline
ats_void_type
atslib_fclose_stdin() {
  atspre_stdin_view_get() ;
  atslib_fclose(stdin) ;
  return ;
}

static inline
ats_void_type
atslib_fclose_stdout() {
  atspre_stdout_view_get() ;
  atslib_fclose(stdout) ;
  return ;
}

static inline
ats_void_type
atslib_fclose_stderr() {
  atspre_stderr_view_get() ;
  atslib_fclose(stderr) ;
  return ;
}

/* ****** ****** */

static inline
ats_int_type
atslib_feof (ats_ptr_type file) {
  return feof ((FILE *)file) ;
}

static inline
ats_int_type
atslib_ferror(ats_ptr_type file) {
  return ferror ((FILE *)file) ;
}

/* ****** ****** */

static inline
ats_int_type
atslib_fflush_err(ats_ptr_type file) {
  return fflush((FILE *)file) ;
}

static inline
ats_void_type
atslib_fflush (ats_ptr_type file) {
  int n = fflush((FILE *)file) ;
  if (n < 0) ats_exit_errmsg (n, "Exit: [fflush] failed\n") ;
  return ;
}

static inline
ats_void_type
atslib_fflush_stdout (void) {
  atspre_stdout_view_get ();
  atslib_fflush (stdout);
  atspre_stdout_view_set () ;
  return ;
}

/* ****** ****** */

static inline
ats_int_type
atslib_fgetc(ats_ptr_type file) {
  return fgetc((FILE *)file) ;
}

static inline
ats_int_type
atslib_getchar () {
  int i ;
  atspre_stdin_view_get ();
  i = getchar ();
  atspre_stdin_view_set () ;
  return i ;
}

/* ****** ****** */

static inline
ats_ptr_type
atslib_fgets_err
  (ats_ptr_type buf, ats_int_type n, ats_ptr_type file) {
  return fgets((char *)buf, (int)n, (FILE *)file) ;
}

static inline
ats_void_type
atslib_fgets
  (ats_ptr_type buf, ats_int_type n, ats_ptr_type file) {
  ats_ptr_type p ;
  p = fgets((char *)buf, (int)n, (FILE *)file) ;
  if (!p) {
    ats_exit_errmsg(errno, "Exit: [fgets] failed\n") ;
  }
  return ;  
}

/* ****** ****** */

static inline
ats_int_type
atslib_fileno(ats_ptr_type file) {
  return fileno((FILE *)file) ;
}

/* ****** ****** */

static inline
ats_ptr_type
atslib_fopen_err(ats_ptr_type name, ats_ptr_type mode) {
  return fopen((char *)name, (char *)mode) ;
}

static inline
ats_ptr_type
atslib_fopen(ats_ptr_type name, ats_ptr_type mode) {
  FILE *file = fopen((char *)name, (char *)mode) ;
  if (!file) {
    atspre_exit_prerrf(
      errno, "Exit: [fopen(\"%s\", \"%s\")] failed\n", name, mode
    ) ;
  }
  return file ;
}

/* ****** ****** */

static inline
ats_int_type
atslib_fputc_err(ats_char_type c, ats_ptr_type file) {
  return fputc((unsigned char)c, (FILE *)file) ;
}

static inline
ats_void_type
atslib_fputc(ats_char_type c, ats_ptr_type file) {
  int n = fputc((unsigned char)c, (FILE *)file) ;
  if (n < 0) {
    atspre_exit_prerrf (errno, "Exit: [fputc(%c)] failed\n", c) ;
  }
  return ;
}

static inline
ats_int_type
atslib_fputs_err(ats_ptr_type s, ats_ptr_type file) {
  return fputs ((char *)s, (FILE *)file) ;
}

static inline
atslib_fputs(ats_ptr_type s, ats_ptr_type file) {
  int n = fputs ((char *)s, (FILE *)file) ;
  if (n < 0) {
    atspre_exit_prerrf (errno, "[Exit: fputs(%s)] failed\n", s) ;
  }
  return ;
}

/* ****** ****** */

static inline
ats_int_type
atslib_fread
  (ats_ptr_type buf, ats_int_type sz, ats_int_type n, ats_ptr_type file)
{
  return fread ((void *)buf, (size_t)sz, (size_t)n, (FILE *)file) ;
}

static inline
ats_int_type
atslib_fread_byte
  (ats_ptr_type buf, ats_int_type n, ats_ptr_type file) {
  return fread ((void *)buf, 1, (size_t)n, (FILE *)file) ;
}

/* ****** ****** */

static inline
ats_ptr_type
atslib_freopen_err
  (ats_ptr_type name, ats_ptr_type mode, ats_ptr_type file) {
  return freopen(name, mode, (FILE *)file) ;
}

static inline
ats_void_type
atslib_freopen
  (ats_ptr_type name, ats_ptr_type mode, ats_ptr_type file) {
  FILE *file_new = freopen(name, mode, (FILE *)file) ;
  if (!file_new) {
    atspre_exit_prerrf (
      errno, "Exit: [freopen(\"%s\", \"%s\")] failed\n", name, mode
    ) ;
  }
  return ;
}

static inline
ats_void_type
atslib_freopen_stdin
  (ats_ptr_type name) {
  FILE *file_new ;
  atspre_stdin_view_get() ;
  file_new = freopen(name, "r", stdin) ;
  if (!file_new) {
    atspre_exit_prerrf (
      errno, "Exit: [freopen_stdin(\"%s\")] failed\n", name
    ) ;
  }
  atspre_stdin_view_set() ;
  return ;
}

static inline
ats_void_type
atslib_freopen_stdout
  (ats_ptr_type name) {
  FILE *file_new ;
  atspre_stdout_view_get () ;
  file_new = freopen(name, "w", stdout) ;
  if (!file_new) {
    atspre_exit_prerrf (
      errno, "Exit: [freopen_stdout(\"%s\")] failed\n", name
    ) ;
  }
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atslib_freopen_stderr
  (ats_ptr_type name) {
  FILE *file_new ;
  atspre_stderr_view_get() ;
  file_new = freopen(name, "w", stderr) ;
  if (!file_new) {
    atspre_exit_prerrf (
      errno, "Exit: [freopen_stderr(\"%s\")] failed\n", name
    ) ;
  }
  atspre_stderr_view_set() ;
  return ;
}

/* ****** ****** */

static inline
ats_lint_type
atslib_ftell(ats_ptr_type file) {
  return ftell((FILE *)file) ;
}

//

static inline
ats_int_type
atslib_fwrite
  (ats_ptr_type buf, ats_int_type sz, ats_int_type n, ats_ptr_type file) {
  return fwrite ((void *)buf, (size_t)sz, (size_t)n, (FILE *)file) ;
}

static inline
ats_int_type
atslib_fwrite_byte
  (ats_ptr_type buf, ats_int_type n, ats_ptr_type file) {
  return fwrite ((void *)buf, 1, (size_t)n, (FILE *)file) ;
}

//

static inline
ats_int_type
atslib_perror(ats_ptr_type msg) {
  atspre_stderr_view_get () ;
  perror ((char *)msg) ;
  atspre_stderr_view_set () ;
  return ;
}

static inline
ats_int_type
atslib_putchar(ats_char_type c) {
  int i ;
  atspre_stdout_view_get () ;
  i = putchar ((unsigned char)c) ;
  atspre_stdout_view_set () ;
  return i ;
}

static inline
ats_int_type
atslib_put_string(ats_ptr_type s) {
  int i ;
  atspre_stdout_view_get () ;
  i = puts ((char *)s) ;
  atspre_stdout_view_set () ;
  return i ;
}

static inline
ats_ptr_type
atslib_tmpfile () { return tmpfile() ; }

static inline
ats_int_type
atslib_ungetc (ats_char_type c, ats_ptr_type file) {
  return ungetc((unsigned char)c, (FILE *)file) ;
}

#endif /* _LIBC_STDIO_CATS */

/* end of [stdio.cats] */
