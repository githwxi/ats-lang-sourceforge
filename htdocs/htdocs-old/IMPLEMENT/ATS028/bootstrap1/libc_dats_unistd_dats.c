/*
 *
 * This C code is generated by ATS/Geizella
 * The compilation time is: 2012-5-27: 21:23
 *
 */

#define _ATS_GEIZELLA 1

#include "ats_config.h"
#include "ats_basics.h"
#include "ats_types.h"
#include "ats_exception.h"
#include "ats_memory.h"

/* include some .cats files */

#include "prelude/CATS/array.cats"
#include "prelude/CATS/basics.cats"
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/printf.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/sizetype.cats"
#include "prelude/CATS/string.cats"

/* external codes at top */



#include <errno.h>
#include <unistd.h>

ats_int_type
atslib_fork_and_exec_and_wait
  (ats_clo_ptr_type f_child) {
  pid_t pid ;
  int status ;

  pid = fork () ;
  if (pid < 0) {
    ats_exit_errmsg (errno, "Exit: [fork] failed.\n") ;
  }
  if (pid > 0) { wait (&status) ; return status ; }
  /* this is the child */
  ((ats_void_type (*)(ats_clo_ptr_type))f_child->closure_fun)(f_child) ;
  exit (0) ;
} // end of [atslib_fork_and_exec_and_wait]

#define __GETCWD_BUFSZ 64

ats_ptr_type
atslib_getcwd0 () {
  char *buf, *res ;
  int sz = __GETCWD_BUFSZ ;
//
  buf = (char*)ATS_MALLOC (__GETCWD_BUFSZ) ;
  while (1) {
    res = getcwd (buf, sz) ;
    if (!res) {
      ATS_FREE (buf) ;
      sz = sz + sz ; buf = (char*)ATS_MALLOC (sz) ;
      continue ;
    }
    break ;
  } // end of [while]
//
  return buf ;
} // end of [atslib_getcwd0]


/* type definitions */

/* external dynamic constructor declarations */

/* external dynamic constant declarations */

/* internal function declarations */

/* sum constructor declarations */

/* exception constructor declarations */

/* global dynamic constant declarations */

/* static temporary variable declarations */

/* function implementations */

/* static load function */

static int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibc_dats_unistd_2edats__staload_flag = 0 ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibc_dats_unistd_2edats__staload () {
if (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibc_dats_unistd_2edats__staload_flag) return ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibc_dats_unistd_2edats__staload_flag = 1 ;
}

/* dynamic load function */

ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibc_dats_unistd_2edats__dynload () {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibc_dats_unistd_2edats__staload () ;
}

/* external types */

/* external codes at mid */

/* external codes at bot */
