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



ATSextfun()
ats_char_type atsopt_charlst_uncons (ats_ref_type) ;

ats_ptr_type
string_make_charlst_rev_int (
  ats_ptr_type cs, ats_int_type n
) {
  char *s;
  s = ATS_MALLOC (n+1) ; s += n ; *s = '\000' ;
  while (!atsopt_charlst_is_nil(cs)) { *--s = atsopt_charlst_uncons(&cs) ; }
  return s ;
} // end of [string_make_charlst_rev_int]


/* type definitions */

typedef struct {
ats_char_type atslab_0 ;
ats_ptr_type atslab_1 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats_sum_0 ;

/* external dynamic constructor declarations */

ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__CHARLSTnil) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__CHARLSTcons) ;

/* external dynamic constant declarations */

extern ats_int_type atspre_iadd(ats_int_type, ats_int_type) ;
extern ats_size_type atspre_add_size1_int1(ats_size_type, ats_int_type) ;
extern ats_char_type atspre_string_get_char_at(ats_ptr_type, ats_size_type) ;
extern ats_bool_type atspre_string_isnot_at_end(ats_ptr_type, ats_size_type) ;
extern ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_free(ats_ptr_type) ;
extern ats_int_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_length(ats_ptr_type) ;
extern ats_ptr_type string_make_charlst_rev_int(ats_ptr_type, ats_int_type) ;
extern ats_bool_type atsopt_charlst_is_nil(ats_ptr_type) ;
extern ats_char_type atsopt_charlst_uncons(ats_ref_type) ;

/* internal function declarations */

static ats_int_type aux_2 (ats_ptr_type arg0, ats_int_type arg1) ;

static ats_ptr_type loop_4 (ats_ptr_type arg0, ats_size_type arg1, ats_ptr_type arg2) ;

/* sum constructor declarations */

/* exception constructor declarations */

/* global dynamic constant declarations */

/* static temporary variable declarations */

/* function implementations */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_free (ats_ptr_type arg0) {
ATSlocal_void(tmp0) ;
ATSlocal(ats_ptr_type, tmp2) ;
ATSlocal(ats_ptr_type, tmp3) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_free:
do {
__ats_lab_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_1 ; }
tmp2 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats_sum_0*)arg0)->atslab_1 ;
ATS_FREE(arg0) ;
tmp3 = tmp2 ;
arg0 = tmp3 ;
goto __ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_free ;
break ;

__ats_lab_1:
break ;

} while (0) ;
return ;
} /* fun */

ats_int_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_length (ats_ptr_type arg0) {
ATSlocal(ats_int_type, tmp5) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_length:
tmp5 = aux_2 (arg0, 0) ;
return tmp5 ;
} /* fun */

ats_int_type
aux_2 (ats_ptr_type arg0, ats_int_type arg1) {
ATSlocal(ats_int_type, tmp6) ;
ATSlocal(ats_ptr_type, tmp8) ;
ATSlocal(ats_ptr_type, tmp9) ;
ATSlocal(ats_ptr_type, tmp10) ;
ATSlocal(ats_int_type, tmp11) ;
__ats_lab_aux_2:
do {
__ats_lab_2:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_3 ; }
tmp8 = &(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats_sum_0*)arg0)->atslab_1) ;
tmp10 = *((ats_ptr_type*)tmp8) ;
tmp9 = tmp10 ;
tmp11 = atspre_iadd (arg1, 1) ;
arg0 = tmp9 ;
arg1 = tmp11 ;
goto __ats_lab_aux_2 ;
break ;

__ats_lab_3:
tmp6 = arg1 ;
break ;

} while (0) ;
return tmp6 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_add_string (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_ptr_type, tmp13) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_add_string:
tmp13 = loop_4 (arg1, 0, arg0) ;
return tmp13 ;
} /* fun */

ats_ptr_type
loop_4 (ats_ptr_type arg0, ats_size_type arg1, ats_ptr_type arg2) {
ATSlocal(ats_ptr_type, tmp14) ;
ATSlocal(ats_bool_type, tmp15) ;
ATSlocal(ats_ptr_type, tmp17) ;
ATSlocal(ats_size_type, tmp18) ;
ATSlocal(ats_ptr_type, tmp19) ;
ATSlocal(ats_char_type, tmp20) ;
__ats_lab_loop_4:
tmp15 = atspre_string_isnot_at_end (arg0, arg1) ;
if (tmp15) {
tmp17 = arg0 ;
tmp18 = atspre_add_size1_int1 (arg1, 1) ;
tmp20 = atspre_string_get_char_at (arg0, arg1) ;
tmp19 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats_sum_0)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats_sum_0*)tmp19)->atslab_0 = tmp20 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats_sum_0*)tmp19)->atslab_1 = arg2 ;

arg0 = tmp17 ;
arg1 = tmp18 ;
arg2 = tmp19 ;
goto __ats_lab_loop_4 ;
} else {
tmp14 = arg2 ;
} /* if */
return tmp14 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__string_make_charlst_rev (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp22) ;
ATSlocal(ats_int_type, tmp23) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__string_make_charlst_rev:
tmp23 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__charlst_length (arg0) ;
tmp22 = string_make_charlst_rev_int (arg0, tmp23) ;
return tmp22 ;
} /* fun */

ats_bool_type
atsopt_charlst_is_nil (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp24) ;
__ats_lab_atsopt_charlst_is_nil:
do {
__ats_lab_4:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_5 ; }
tmp24 = ats_false_bool ;
break ;

__ats_lab_5:
tmp24 = ats_true_bool ;
break ;

} while (0) ;
return tmp24 ;
} /* fun */

ats_char_type
atsopt_charlst_uncons (ats_ref_type arg0) {
ATSlocal(ats_char_type, tmp27) ;
ATSlocal(ats_char_type, tmp28) ;
ATSlocal(ats_ptr_type, tmp29) ;
__ats_lab_atsopt_charlst_uncons:
tmp28 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats_sum_0*)*((ats_ptr_type*)arg0))->atslab_0 ;
tmp29 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats_sum_0*)*((ats_ptr_type*)arg0))->atslab_1 ;
ATS_FREE(*((ats_ptr_type*)arg0)) ;
*((ats_ptr_type*)arg0) = tmp29 ;
tmp27 = tmp28 ;
return tmp27 ;
} /* fun */

/* static load function */

extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__staload () ;
static int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats__staload_flag = 0 ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats__staload () {
if (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats__staload_flag) return ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats__staload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2esats__staload () ;
}

/* dynamic load function */

extern int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats__dynload_flag ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats__dynload () {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats__dynload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_charlst_2edats__staload () ;
}

/* external types */

/* external codes at mid */

/* external codes at bot */

