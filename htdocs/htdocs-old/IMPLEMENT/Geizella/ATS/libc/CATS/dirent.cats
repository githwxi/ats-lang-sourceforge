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

#ifndef _LIBC_DIRENT_CATS
#define _LIBC_DIRENT_CATS

/* ****** ****** */

#include <errno.h>
#include <sys/types.h>
#include <dirent.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

typedef DIR ats_DIR_type ;
typedef struct dirent ats_dirent_type ;
typedef off_t ats_off_t_type ;

/* ****** ****** */

static inline
ats_int_type
atslib_closedir_err (ats_ptr_type dir) {
  return closedir (dir) ;
}

static inline
ats_void_type
atslib_closedir (ats_ptr_type dir) {
  int res ;
  res = closedir (dir) ;
  if (res < 0) {
    perror ("closedir") ;
    ats_exit_errmsg (errno, "Exit: [closedir] failed.\n") ;
  }
  return ;
}

static inline
ats_ptr_type
atslib_opendir_err(ats_ptr_type name) {
  return opendir (name) ;
}

static inline
ats_ptr_type
atslib_opendir (ats_ptr_type name) {
  DIR* res ;
  res = opendir (name) ;
  if (!res) {
    perror ("opendir") ;
    atspre_exit_prerrf (
      errno, "Exit: [opendir(%s)] failed.\n", name
    ) ;
  }
  return res ;
}

static inline
ats_ptr_type
atslib_readdir_err (ats_ptr_type dir) {
  return readdir ((DIR *)dir) ;
}

/* ****** ****** */

#endif /* _LIBC_DIRENT_CATS */
