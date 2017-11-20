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

typedef struct {
int tag ;
ats_int_type atslab_0 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1 ;

typedef struct {
ats_ptr_type atslab_0 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_2 ;

typedef struct {
ats_int_type atslab_0 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_3 ;

/* external dynamic constructor declarations */

ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__None_vt) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__Some_vt) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__LABint) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__LABsym) ;

/* external dynamic constant declarations */

extern ats_ptr_type atspre_stdout_get() ;
extern ats_void_type atspre_stdout_view_set() ;
extern ats_ptr_type atspre_stderr_get() ;
extern ats_void_type atspre_stderr_view_set() ;
extern ats_bool_type atspre_eq_int_int(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_neq_int_int(ats_int_type, ats_int_type) ;
extern ats_int_type atspre_compare_int_int(ats_int_type, ats_int_type) ;
extern ats_void_type atspre_fprint_int(ats_ref_type, ats_int_type) ;
extern ats_bool_type atspre_ilt(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_ilte(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_igt(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_igte(ats_int_type, ats_int_type) ;
extern ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__symbol_make_string(ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__eq_symbol_symbol(ats_ptr_type, ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__neq_symbol_symbol(ats_ptr_type, ats_ptr_type) ;
extern ats_int_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__compare_symbol_symbol(ats_ptr_type, ats_ptr_type) ;
extern ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__fprint_symbol(ats_ref_type, ats_ptr_type) ;
extern ats_int_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__compare_label_label(ats_ptr_type, ats_ptr_type) ;
extern ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__fprint_label(ats_ref_type, ats_ptr_type) ;

/* internal function declarations */

/* sum constructor declarations */

ATSglobal(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__LABint) ;
ATSglobal(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__LABsym) ;

/* exception constructor declarations */

/* global dynamic constant declarations */

/* static temporary variable declarations */

/* function implementations */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_make_int (ats_int_type arg0) {
ATSlocal(ats_ptr_type, tmp0) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_make_int:
tmp0 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0)) ;
((ats_sum_ptr_type)tmp0)->tag = 0 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0*)tmp0)->atslab_0 = arg0 ;

return tmp0 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_make_string (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp1) ;
ATSlocal(ats_ptr_type, tmp2) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_make_string:
tmp2 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__symbol_make_string (arg0) ;
tmp1 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1)) ;
((ats_sum_ptr_type)tmp1)->tag = 1 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)tmp1)->atslab_0 = tmp2 ;

return tmp1 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_make_sym (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp3) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_make_sym:
tmp3 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1)) ;
((ats_sum_ptr_type)tmp3)->tag = 1 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)tmp3)->atslab_0 = arg0 ;

return tmp3 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_get_sym (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp4) ;
ATSlocal(ats_ptr_type, tmp6) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_get_sym:
do {
__ats_lab_0:
if (((ats_sum_ptr_type)arg0)->tag != 1) { goto __ats_lab_1 ; }
tmp6 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)arg0)->atslab_0 ;
tmp4 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_2)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_2*)tmp4)->atslab_0 = tmp6 ;

break ;

__ats_lab_1:
tmp4 = (ats_sum_ptr_type)0 ;

break ;

} while (0) ;
return tmp4 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_get_int (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp8) ;
ATSlocal(ats_int_type, tmp10) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__label_get_int:
do {
__ats_lab_2:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_3 ; }
tmp10 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0*)arg0)->atslab_0 ;
tmp8 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_3)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_3*)tmp8)->atslab_0 = tmp10 ;

break ;

__ats_lab_3:
tmp8 = (ats_sum_ptr_type)0 ;

break ;

} while (0) ;
return tmp8 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__lt_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp12) ;
ATSlocal(ats_int_type, tmp13) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__lt_label_label:
tmp13 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__compare_label_label (arg0, arg1) ;
tmp12 = atspre_ilt (tmp13, 0) ;
return tmp12 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__lte_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp14) ;
ATSlocal(ats_int_type, tmp15) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__lte_label_label:
tmp15 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__compare_label_label (arg0, arg1) ;
tmp14 = atspre_ilte (tmp15, 0) ;
return tmp14 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__gt_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp16) ;
ATSlocal(ats_int_type, tmp17) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__gt_label_label:
tmp17 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__compare_label_label (arg0, arg1) ;
tmp16 = atspre_igt (tmp17, 0) ;
return tmp16 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__gte_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp18) ;
ATSlocal(ats_int_type, tmp19) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__gte_label_label:
tmp19 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__compare_label_label (arg0, arg1) ;
tmp18 = atspre_igte (tmp19, 0) ;
return tmp18 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__eq_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp20) ;
ATSlocal(ats_int_type, tmp22) ;
ATSlocal(ats_int_type, tmp23) ;
ATSlocal(ats_ptr_type, tmp25) ;
ATSlocal(ats_ptr_type, tmp26) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__eq_label_label:
do {
__ats_lab_4:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_5 ; }
tmp22 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0*)arg0)->atslab_0 ;
if (((ats_sum_ptr_type)arg1)->tag != 0) { goto __ats_lab_5 ; }
tmp23 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0*)arg1)->atslab_0 ;
tmp20 = atspre_eq_int_int (tmp22, tmp23) ;
break ;

__ats_lab_5:
if (((ats_sum_ptr_type)arg0)->tag != 1) { goto __ats_lab_6 ; }
tmp25 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)arg0)->atslab_0 ;
if (((ats_sum_ptr_type)arg1)->tag != 1) { goto __ats_lab_6 ; }
tmp26 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)arg1)->atslab_0 ;
tmp20 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__eq_symbol_symbol (tmp25, tmp26) ;
break ;

__ats_lab_6:
tmp20 = ats_false_bool ;
break ;

} while (0) ;
return tmp20 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__neq_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp28) ;
ATSlocal(ats_int_type, tmp30) ;
ATSlocal(ats_int_type, tmp31) ;
ATSlocal(ats_ptr_type, tmp33) ;
ATSlocal(ats_ptr_type, tmp34) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__neq_label_label:
do {
__ats_lab_7:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_8 ; }
tmp30 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0*)arg0)->atslab_0 ;
if (((ats_sum_ptr_type)arg1)->tag != 0) { goto __ats_lab_8 ; }
tmp31 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0*)arg1)->atslab_0 ;
tmp28 = atspre_neq_int_int (tmp30, tmp31) ;
break ;

__ats_lab_8:
if (((ats_sum_ptr_type)arg0)->tag != 1) { goto __ats_lab_9 ; }
tmp33 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)arg0)->atslab_0 ;
if (((ats_sum_ptr_type)arg1)->tag != 1) { goto __ats_lab_9 ; }
tmp34 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)arg1)->atslab_0 ;
tmp28 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__neq_symbol_symbol (tmp33, tmp34) ;
break ;

__ats_lab_9:
tmp28 = ats_true_bool ;
break ;

} while (0) ;
return tmp28 ;
} /* fun */

ats_int_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__compare_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_int_type, tmp36) ;
ATSlocal(ats_int_type, tmp38) ;
ATSlocal(ats_int_type, tmp39) ;
ATSlocal(ats_ptr_type, tmp41) ;
ATSlocal(ats_ptr_type, tmp42) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__compare_label_label:
do {
__ats_lab_10:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_11 ; }
tmp38 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0*)arg0)->atslab_0 ;
if (((ats_sum_ptr_type)arg1)->tag != 0) { goto __ats_lab_11 ; }
tmp39 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0*)arg1)->atslab_0 ;
tmp36 = atspre_compare_int_int (tmp38, tmp39) ;
break ;

__ats_lab_11:
if (((ats_sum_ptr_type)arg0)->tag != 1) { goto __ats_lab_12 ; }
tmp41 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)arg0)->atslab_0 ;
if (((ats_sum_ptr_type)arg1)->tag != 1) { goto __ats_lab_12 ; }
tmp42 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)arg1)->atslab_0 ;
tmp36 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__compare_symbol_symbol (tmp41, tmp42) ;
break ;

__ats_lab_12:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_13 ; }
if (((ats_sum_ptr_type)arg1)->tag != 1) { goto __ats_lab_13 ; }
tmp36 = -1 ;
break ;

__ats_lab_13:
tmp36 = 1 ;
break ;

} while (0) ;
return tmp36 ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__fprint_label (ats_ref_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp45) ;
ATSlocal(ats_int_type, tmp47) ;
ATSlocal(ats_ptr_type, tmp49) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__fprint_label:
do {
__ats_lab_14:
if (((ats_sum_ptr_type)arg1)->tag != 0) { goto __ats_lab_15 ; }
tmp47 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_0*)arg1)->atslab_0 ;
/* tmp45 = */ atspre_fprint_int (arg0, tmp47) ;
break ;

__ats_lab_15:
tmp49 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats_sum_1*)arg1)->atslab_0 ;
/* tmp45 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__fprint_symbol (arg0, tmp49) ;
break ;

} while (0) ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__print_label (ats_ptr_type arg0) {
ATSlocal_void(tmp50) ;
ATSlocal(ats_ptr_type, tmp51) ;
ATSlocal(ats_ptr_type, tmp52) ;
ATSlocal_void(tmp53) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__print_label:
tmp51 = atspre_stdout_get () ;
tmp52 = (tmp51) ;
/* tmp53 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__fprint_label (tmp52, arg0) ;
/* tmp50 = */ atspre_stdout_view_set () ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__prerr_label (ats_ptr_type arg0) {
ATSlocal_void(tmp54) ;
ATSlocal(ats_ptr_type, tmp55) ;
ATSlocal(ats_ptr_type, tmp56) ;
ATSlocal_void(tmp57) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__prerr_label:
tmp55 = atspre_stderr_get () ;
tmp56 = (tmp55) ;
/* tmp57 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__fprint_label (tmp56, arg0) ;
/* tmp54 = */ atspre_stderr_view_set () ;
return ;
} /* fun */

/* static load function */

extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__staload () ;
static int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__staload_flag = 0 ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__staload () {
if (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__staload_flag) return ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__staload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__LABint.tag = 0 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__LABsym.tag = 1 ;
}

/* dynamic load function */

extern int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__dynload_flag ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__dynload () {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__dynload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_label_2edats__staload () ;
}

/* external types */

/* external codes at mid */

/* external codes at bot */

