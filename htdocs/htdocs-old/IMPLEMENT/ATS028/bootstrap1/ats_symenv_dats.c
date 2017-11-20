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
ats_ptr_type atslab_map ;
ats_ptr_type atslab_maplst ;
ats_ptr_type atslab_savedlst ;
ats_ptr_type atslab_pervasive ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_1 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_2 ;

typedef struct {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_2 atslab_0 ;
ats_ptr_type atslab_1 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_3 ;

/* external dynamic constructor declarations */

ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__list_vt_cons) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__list_vt_nil) ;

/* external dynamic constant declarations */

extern ats_int_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__compare_symbol_symbol(ats_ptr_type, ats_ptr_type) ;
extern ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_map_lin_2esats__map_make(ats_ptr_type) ;
extern ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symmap_make() ;
extern ats_ptr_type atspre_ref_make_elt_tsz(ats_ref_type, ats_size_type) ;
extern ats_ptr_type atspre_ref_get_view_ptr(ats_ptr_type) ;

/* internal function declarations */

static ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type (ats_ptr_type arg0) ;

static ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_swap__ats_ptr_type (ats_ptr_type arg0, ats_ref_type arg1) ;

/* sum constructor declarations */

/* exception constructor declarations */

/* global dynamic constant declarations */

/* static temporary variable declarations */

/* function implementations */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symmap_make () {
ATSlocal(ats_ptr_type, tmp0) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symmap_make:
tmp0 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_map_lin_2esats__map_make ((&_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__compare_symbol_symbol)) ;
return tmp0 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_make () {
ATSlocal(ats_ptr_type, tmp1) ;
ATSlocal(ats_ptr_type, tmp2) ;
ATSlocal(ats_ptr_type, tmp5) ;
ATSlocal(ats_ptr_type, tmp6) ;
ATSlocal(ats_ptr_type, tmp7) ;
ATSlocal(ats_ptr_type, tmp8) ;
ATSlocal(ats_ptr_type, tmp9) ;
ATSlocal(ats_ptr_type, tmp10) ;
ATSlocal(ats_ptr_type, tmp11) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_make:
tmp5 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symmap_make () ;
tmp2 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type (tmp5) ;
tmp7 = (ats_sum_ptr_type)0 ;

tmp6 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type (tmp7) ;
tmp9 = (ats_sum_ptr_type)0 ;

tmp8 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type (tmp9) ;
tmp11 = (ats_sum_ptr_type)0 ;

tmp10 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type (tmp11) ;
tmp1 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)tmp1)->atslab_map = tmp2 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)tmp1)->atslab_maplst = tmp6 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)tmp1)->atslab_savedlst = tmp8 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)tmp1)->atslab_pervasive = tmp10 ;

return tmp1 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp3) ;
ATSlocal(ats_ptr_type, tmp4) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type:
tmp4 = arg0 ;
tmp3 = atspre_ref_make_elt_tsz ((&tmp4), sizeof(ats_ptr_type)) ;
return tmp3 ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_push (ats_ptr_type arg0) {
ATSlocal_void(tmp12) ;
ATSlocal(ats_ptr_type, tmp13) ;
ATSlocal(ats_ptr_type, tmp14) ;
ATSlocal(ats_ptr_type, tmp15) ;
ATSlocal(ats_ptr_type, tmp16) ;
ATSlocal(ats_ptr_type, tmp17) ;
ATSlocal(ats_ptr_type, tmp19) ;
ATSlocal(ats_ptr_type, tmp20) ;
ATSlocal(ats_ptr_type, tmp21) ;
ATSlocal(ats_ptr_type, tmp22) ;
ATSlocal(ats_ptr_type, tmp23) ;
ATSlocal(ats_ptr_type, tmp24) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_push:
tmp15 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)arg0)->atslab_map ;
tmp14 = atspre_ref_get_view_ptr (tmp15) ;
tmp16 = (tmp14) ;
tmp17 = *((ats_ptr_type*)tmp16) ;
tmp19 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symmap_make () ;
*((ats_ptr_type*)tmp16) = tmp19 ;
tmp13 = tmp17 ;
tmp21 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)arg0)->atslab_maplst ;
tmp20 = atspre_ref_get_view_ptr (tmp21) ;
tmp22 = (tmp20) ;
tmp24 = *((ats_ptr_type*)tmp22) ;
tmp23 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_1)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_1*)tmp23)->atslab_0 = tmp13 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_1*)tmp23)->atslab_1 = tmp24 ;

*((ats_ptr_type*)tmp22) = tmp23 ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_swap (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp25) ;
ATSlocal(ats_ptr_type, tmp26) ;
ATSlocal(ats_ptr_type, tmp27) ;
ATSlocal(ats_ptr_type, tmp28) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_swap:
tmp27 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)arg0)->atslab_map ;
tmp26 = atspre_ref_get_view_ptr (tmp27) ;
tmp28 = (tmp26) ;
/* tmp25 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_swap__ats_ptr_type (arg1, tmp28) ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_swap__ats_ptr_type (ats_ptr_type arg0, ats_ref_type arg1) {
ATSlocal_void(tmp29) ;
ATSlocal(ats_ptr_type, tmp30) ;
ATSlocal(ats_ptr_type, tmp31) ;
ATSlocal(ats_ptr_type, tmp32) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_swap__ats_ptr_type:
tmp30 = atspre_ref_get_view_ptr (arg0) ;
tmp31 = (tmp30) ;
tmp32 = *((ats_ptr_type*)tmp31) ;
*((ats_ptr_type*)tmp31) = *((ats_ptr_type*)arg1) ;
*((ats_ptr_type*)arg1) = tmp32 ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_save (ats_ptr_type arg0) {
ATSlocal_void(tmp34) ;
ATSlocal(ats_ptr_type, tmp35) ;
ATSlocal(ats_ptr_type, tmp36) ;
ATSlocal(ats_ptr_type, tmp37) ;
ATSlocal(ats_ptr_type, tmp38) ;
ATSlocal(ats_ptr_type, tmp39) ;
ATSlocal(ats_ptr_type, tmp41) ;
ATSlocal(ats_ptr_type, tmp42) ;
ATSlocal(ats_ptr_type, tmp43) ;
ATSlocal(ats_ptr_type, tmp44) ;
ATSlocal(ats_ptr_type, tmp45) ;
ATSlocal(ats_ptr_type, tmp46) ;
ATSlocal(ats_ptr_type, tmp48) ;
ATSlocal(ats_ptr_type, tmp49) ;
ATSlocal(ats_ptr_type, tmp50) ;
ATSlocal(ats_ptr_type, tmp51) ;
ATSlocal(ats_ptr_type, tmp52) ;
ATSlocal(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_2, tmp53) ;
ATSlocal(ats_ptr_type, tmp54) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_save:
tmp37 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)arg0)->atslab_map ;
tmp36 = atspre_ref_get_view_ptr (tmp37) ;
tmp38 = (tmp36) ;
tmp39 = *((ats_ptr_type*)tmp38) ;
tmp41 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symmap_make () ;
*((ats_ptr_type*)tmp38) = tmp41 ;
tmp35 = tmp39 ;
tmp44 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)arg0)->atslab_maplst ;
tmp43 = atspre_ref_get_view_ptr (tmp44) ;
tmp45 = (tmp43) ;
tmp46 = *((ats_ptr_type*)tmp45) ;
tmp48 = (ats_sum_ptr_type)0 ;

*((ats_ptr_type*)tmp45) = tmp48 ;
tmp42 = tmp46 ;
tmp50 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)arg0)->atslab_savedlst ;
tmp49 = atspre_ref_get_view_ptr (tmp50) ;
tmp51 = (tmp49) ;
tmp53.atslab_0 = tmp35 ;
tmp53.atslab_1 = tmp42 ;

tmp54 = *((ats_ptr_type*)tmp51) ;
tmp52 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_3)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_3*)tmp52)->atslab_0 = tmp53 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_3*)tmp52)->atslab_1 = tmp54 ;

*((ats_ptr_type*)tmp51) = tmp52 ;
return ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_top_get (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp55) ;
ATSlocal(ats_ptr_type, tmp56) ;
ATSlocal(ats_ptr_type, tmp57) ;
ATSlocal(ats_ptr_type, tmp58) ;
ATSlocal(ats_ptr_type, tmp59) ;
ATSlocal(ats_ptr_type, tmp61) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_top_get:
tmp56 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)arg0)->atslab_map ;
tmp57 = atspre_ref_get_view_ptr (tmp56) ;
tmp58 = (tmp57) ;
tmp59 = *((ats_ptr_type*)tmp58) ;
tmp61 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symmap_make () ;
*((ats_ptr_type*)tmp58) = tmp61 ;
tmp55 = tmp59 ;
return tmp55 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_reftop_get (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp62) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_reftop_get:
tmp62 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)arg0)->atslab_map ;
return tmp62 ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_pervasive_add (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp63) ;
ATSlocal(ats_ptr_type, tmp64) ;
ATSlocal(ats_ptr_type, tmp65) ;
ATSlocal(ats_ptr_type, tmp66) ;
ATSlocal(ats_ptr_type, tmp67) ;
ATSlocal(ats_ptr_type, tmp68) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__symenv_pervasive_add:
tmp65 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_rec_0*)arg0)->atslab_pervasive ;
tmp64 = atspre_ref_get_view_ptr (tmp65) ;
tmp66 = (tmp64) ;
tmp68 = *((ats_ptr_type*)tmp66) ;
tmp67 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_1)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_1*)tmp67)->atslab_0 = arg1 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats_sum_1*)tmp67)->atslab_1 = tmp68 ;

*((ats_ptr_type*)tmp66) = tmp67 ;
return ;
} /* fun */

/* static load function */

extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_map_lin_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2edats__staload () ;
static int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats__staload_flag = 0 ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats__staload () {
if (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats__staload_flag) return ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats__staload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_map_lin_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2edats__staload () ;
}

/* dynamic load function */

extern int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats__dynload_flag ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats__dynload () {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats__dynload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symenv_2edats__staload () ;
}

/* external types */

/* external codes at mid */

/* external codes at bot */

