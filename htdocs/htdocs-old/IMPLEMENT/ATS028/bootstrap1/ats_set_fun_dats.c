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

/* type definitions */

/* external dynamic constructor declarations */

ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__E) ;

/* external dynamic constant declarations */


/* internal function declarations */

/* sum constructor declarations */

ATSglobal(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__E) ;
ATSglobal(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__Bl) ;
ATSglobal(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__Br) ;

/* exception constructor declarations */

/* global dynamic constant declarations */

ATSglobal(ats_ptr_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2esats__set_nil) ;
/* static temporary variable declarations */

ATSstatic(ats_ptr_type, tmp0) ;

/* function implementations */

/* static load function */

extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2esats__staload () ;
static int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__staload_flag = 0 ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__staload () {
if (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__staload_flag) return ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__staload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__E.tag = 0 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__Bl.tag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__Br.tag = 2 ;
}

/* dynamic load function */

extern int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__dynload_flag ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__dynload () {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__dynload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__staload () ;
ats_gc_markroot(&tmp0, sizeof(ats_ptr_type)) ;
tmp0 = (ats_sum_ptr_type)(&_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2edats__E) ;

ats_gc_markroot (&_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2esats__set_nil, sizeof(ats_ptr_type)) ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_set_fun_2esats__set_nil = tmp0 ;
}

/* external types */

/* external codes at mid */

/* external codes at bot */
