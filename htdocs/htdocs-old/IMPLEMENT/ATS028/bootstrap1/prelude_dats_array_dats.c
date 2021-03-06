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


#include "prelude/CATS/array.cats"

/* type definitions */

typedef struct {
ats_ptr_type atslab_2 ;
ats_int_type atslab_3 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fprelude_dats_array_2edats_rec_0 ;

/* external dynamic constructor declarations */

/* external dynamic constant declarations */

extern ats_void_type atspre_vbox_make_view_ptr(ats_ptr_type) ;

/* internal function declarations */

/* sum constructor declarations */

/* exception constructor declarations */

/* global dynamic constant declarations */

ATSglobal(ats_fun_ptr_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fSATS_2farray_2esats__array_get_view_ptr) ;
/* static temporary variable declarations */

/* function implementations */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fSATS_2farray_2esats__array_make_arrsz (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fprelude_dats_array_2edats_rec_0 arg0) {
ATSlocal(ats_ptr_type, tmp0) ;
ATSlocal_void(tmp1) ;
ATSlocal(ats_ptr_type, tmp2) ;
ATSlocal_void(tmp3) ;
ATSlocal(ats_ptr_type, tmp4) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fSATS_2farray_2esats__array_make_arrsz:
tmp2 = ((arg0).atslab_2) ;
/* tmp1 = */ atspre_vbox_make_view_ptr (tmp2) ;
/* tmp3 = (tmp1) */;
tmp4 = ((arg0).atslab_2) ;
tmp0 = tmp4 ;
return tmp0 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fSATS_2farray_2esats__array_get_view_ptr_fun (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp5) ;
ATSlocal(ats_ptr_type, tmp6) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fSATS_2farray_2esats__array_get_view_ptr_fun:
tmp6 = (arg0) ;
tmp5 = tmp6 ;
return tmp5 ;
} /* fun */

/* static load function */

static int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fprelude_dats_array_2edats__staload_flag = 0 ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fprelude_dats_array_2edats__staload () {
if (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fprelude_dats_array_2edats__staload_flag) return ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fprelude_dats_array_2edats__staload_flag = 1 ;
}

/* dynamic load function */

ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fprelude_dats_array_2edats__dynload () {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fprelude_dats_array_2edats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fSATS_2farray_2esats__array_get_view_ptr = &_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fSATS_2farray_2esats__array_get_view_ptr_fun ;
}

/* external types */

/* external codes at mid */

/* external codes at bot */



typedef unsigned char byte ;

ats_void_type
atspre_array_ptr_initialize_elt_tsz (
   ats_ptr_type A
 , ats_size_type asz 
 , ats_ptr_type ini
 , ats_size_type tsz
 )  {
  int i, itsz ; int left ; ats_ptr_type p ;
  if (asz == 0) return ;
  memcpy (A, ini, tsz) ;
  i = 1 ; itsz = tsz ; left = asz - i ;
  while (left > 0) {
    p = (ats_ptr_type)(((byte*)A) + itsz) ;
    if (left <= i) {
      memcpy (p, A, left * tsz) ; return ;
    } /* end of [if] */
    memcpy (p, A, itsz);
    i = i + i ; itsz = itsz + itsz ; left = asz - i ;
  } /* end of [while] */
  return ;
} /* end of [atspre_array_ptr_initialize_elt_tsz] */


