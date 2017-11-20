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


#include "ats_counter.cats" /* only needed for [ATS/Geizella] */

/* type definitions */

/* external dynamic constructor declarations */

/* external dynamic constant declarations */

extern ats_ptr_type atspre_stdout_get() ;
extern ats_void_type atspre_stdout_view_set() ;
extern ats_ptr_type atspre_stderr_get() ;
extern ats_void_type atspre_stderr_view_set() ;
extern ats_bool_type atspre_ilt(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_ilte(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_igt(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_igte(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_ieq(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_ineq(ats_int_type, ats_int_type) ;
extern ats_int_type atsopt_compare_count_count(atsopt_count_type, atsopt_count_type) ;
extern ats_void_type atsopt_fprint_count(ats_ref_type, atsopt_count_type) ;

/* internal function declarations */

/* sum constructor declarations */

/* exception constructor declarations */

/* global dynamic constant declarations */

/* static temporary variable declarations */

/* function implementations */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__lt_count_count (atsopt_count_type arg0, atsopt_count_type arg1) {
ATSlocal(ats_bool_type, tmp0) ;
ATSlocal(ats_int_type, tmp1) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__lt_count_count:
tmp1 = atsopt_compare_count_count (arg0, arg1) ;
tmp0 = atspre_ilt (tmp1, 0) ;
return tmp0 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__lte_count_count (atsopt_count_type arg0, atsopt_count_type arg1) {
ATSlocal(ats_bool_type, tmp2) ;
ATSlocal(ats_int_type, tmp3) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__lte_count_count:
tmp3 = atsopt_compare_count_count (arg0, arg1) ;
tmp2 = atspre_ilte (tmp3, 0) ;
return tmp2 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__gt_count_count (atsopt_count_type arg0, atsopt_count_type arg1) {
ATSlocal(ats_bool_type, tmp4) ;
ATSlocal(ats_int_type, tmp5) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__gt_count_count:
tmp5 = atsopt_compare_count_count (arg0, arg1) ;
tmp4 = atspre_igt (tmp5, 0) ;
return tmp4 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__gte_count_count (atsopt_count_type arg0, atsopt_count_type arg1) {
ATSlocal(ats_bool_type, tmp6) ;
ATSlocal(ats_int_type, tmp7) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__gte_count_count:
tmp7 = atsopt_compare_count_count (arg0, arg1) ;
tmp6 = atspre_igte (tmp7, 0) ;
return tmp6 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__eq_count_count (atsopt_count_type arg0, atsopt_count_type arg1) {
ATSlocal(ats_bool_type, tmp8) ;
ATSlocal(ats_int_type, tmp9) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__eq_count_count:
tmp9 = atsopt_compare_count_count (arg0, arg1) ;
tmp8 = atspre_ieq (tmp9, 0) ;
return tmp8 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__neq_count_count (atsopt_count_type arg0, atsopt_count_type arg1) {
ATSlocal(ats_bool_type, tmp10) ;
ATSlocal(ats_int_type, tmp11) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__neq_count_count:
tmp11 = atsopt_compare_count_count (arg0, arg1) ;
tmp10 = atspre_ineq (tmp11, 0) ;
return tmp10 ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__print_count (atsopt_count_type arg0) {
ATSlocal_void(tmp12) ;
ATSlocal(ats_ptr_type, tmp13) ;
ATSlocal(ats_ptr_type, tmp14) ;
ATSlocal_void(tmp15) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__print_count:
tmp13 = atspre_stdout_get () ;
tmp14 = (tmp13) ;
/* tmp15 = */ atsopt_fprint_count (tmp14, arg0) ;
/* tmp12 = */ atspre_stdout_view_set () ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__prerr_count (atsopt_count_type arg0) {
ATSlocal_void(tmp16) ;
ATSlocal(ats_ptr_type, tmp17) ;
ATSlocal(ats_ptr_type, tmp18) ;
ATSlocal_void(tmp19) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__prerr_count:
tmp17 = atspre_stderr_get () ;
tmp18 = (tmp17) ;
/* tmp19 = */ atsopt_fprint_count (tmp18, arg0) ;
/* tmp16 = */ atspre_stderr_view_set () ;
return ;
} /* fun */

/* static load function */

extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__staload () ;
static int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2edats__staload_flag = 0 ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2edats__staload () {
if (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2edats__staload_flag) return ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2edats__staload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2esats__staload () ;
}

/* dynamic load function */

extern int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2edats__dynload_flag ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2edats__dynload () {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2edats__dynload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_counter_2edats__staload () ;
}

/* external types */

/* external codes at mid */

/* external codes at bot */
