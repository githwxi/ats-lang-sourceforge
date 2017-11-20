/*
 *
 * This C code is generated by ATS/Geizella
 * The compilation time is: 2012-5-27: 21:24
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

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0 ;

typedef struct {
ats_ptr_type atslab_s2exp_srt ;
ats_ptr_type atslab_s2exp_node ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_1 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_2 ;

typedef struct {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_2 atslab_0 ;
ats_ptr_type atslab_1 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_3 ;

typedef struct {
ats_ptr_type atslab_0 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
ats_int_type atslab_1 ;
ats_ptr_type atslab_2 ;
ats_int_type atslab_3 ;
ats_ptr_type atslab_4 ;
ats_ptr_type atslab_5 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_5 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
ats_ptr_type atslab_2 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_6 ;

typedef struct {
atsopt_count_type atslab_0 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_7 ;

typedef struct {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_2 atslab_0 ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_8 ;

/* external dynamic constructor declarations */

ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__list_cons) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__list_nil) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__None) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__Some) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__list_vt_cons) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__list_vt_nil) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__None_vt) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__Some_vt) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__S2Efun) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__S2Emetfn) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__S2Euni) ;

/* external dynamic constant declarations */

extern ats_void_type atspre_prerr_newline() ;
extern ats_bool_type atspre_gt_int_int(ats_int_type, ats_int_type) ;
extern ats_void_type atspre_prerr_string(ats_ptr_type) ;
extern ats_var_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__abort() ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_stamp_2esats__eq_stamp_stamp(atsopt_count_type, atsopt_count_type) ;
ATSextern(ats_ptr_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__s2rt_int) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__lte_s2rt_s2rt(ats_ptr_type, ats_ptr_type) ;
extern ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__s2exp_fun_srt(ats_ptr_type, ats_ptr_type, ats_int_type, ats_ptr_type, ats_int_type, ats_ptr_type, ats_ptr_type) ;
extern ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__s2exp_metfn(ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
extern ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__s2exp_uni(ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
extern atsopt_count_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2var_get_stamp(ats_ptr_type) ;
extern ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__c3str_metric_nat(ats_ptr_type, ats_ptr_type) ;
extern ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__trans3_env_add_cstr(ats_ptr_type) ;
extern ats_ptr_type atspre_ref_make_elt_tsz(ats_ref_type, ats_size_type) ;
extern ats_ptr_type atspre_ref_get_view_ptr(ats_ptr_type) ;

/* internal function declarations */

static ats_void_type aux_1 (ats_ptr_type arg0, ats_ptr_type arg1) ;

static ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type (ats_ptr_type arg0) ;

static ats_bool_type aux1_4 (ats_ptr_type arg0, atsopt_count_type arg1) ;

static ats_ptr_type aux2_5 (ats_ptr_type arg0, atsopt_count_type arg1) ;

static ats_ptr_type aux_9 (ats_ptr_type env0, ats_ptr_type arg0, ats_ref_type arg1) ;
static ats_ptr_type aux_9_clofun (ats_clo_ptr_type clo, ats_ptr_type arg0, ats_ref_type arg1) ;
static ats_clo_ptr_type aux_9_clo_make (ats_ptr_type env0) ;

static ats_ptr_type aux_10 (ats_ptr_type arg0) ;

/* sum constructor declarations */

/* exception constructor declarations */

ATSglobal(ats_exn_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__FatalErrorException) ;
ATSglobal(ats_exn_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__DeadCodeException) ;
ATSglobal(ats_exn_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibats_lex_lexing_2esats__LexingErrorException) ;

/* global dynamic constant declarations */

/* static temporary variable declarations */

ATSstatic(ats_ptr_type, tmp14) ;
ATSstatic(ats_ptr_type, tmp17) ;

/* function implementations */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__metric_nat_check (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp0) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__metric_nat_check:
/* tmp0 = */ aux_1 (arg0, arg1) ;
return ;
} /* fun */

ats_void_type
aux_1 (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp1) ;
ATSlocal(ats_ptr_type, tmp3) ;
ATSlocal(ats_ptr_type, tmp4) ;
ATSlocal_void(tmp5) ;
ATSlocal(ats_bool_type, tmp6) ;
ATSlocal(ats_ptr_type, tmp7) ;
ATSlocal(ats_ptr_type, tmp9) ;
ATSlocal(ats_ptr_type, tmp11) ;
ATSlocal(ats_ptr_type, tmp12) ;
__ats_lab_aux_1:
do {
__ats_lab_0:
if (arg1 == (ats_sum_ptr_type)0) { goto __ats_lab_1 ; }
tmp3 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0*)arg1)->atslab_0 ;
tmp4 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0*)arg1)->atslab_1 ;
tmp7 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_1*)tmp3)->atslab_s2exp_srt ;
tmp6 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__lte_s2rt_s2rt (tmp7, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__s2rt_int) ;
if (tmp6) {
tmp9 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__c3str_metric_nat (arg0, tmp3) ;
/* tmp5 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__trans3_env_add_cstr (tmp9) ;
} else {
} /* if */
tmp11 = arg0 ;
tmp12 = tmp4 ;
arg0 = tmp11 ;
arg1 = tmp12 ;
goto __ats_lab_aux_1 ;
break ;

__ats_lab_1:
break ;

} while (0) ;
return ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp15) ;
ATSlocal(ats_ptr_type, tmp16) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type:
tmp16 = arg0 ;
tmp15 = atspre_ref_make_elt_tsz ((&tmp16), sizeof(ats_ptr_type)) ;
return tmp15 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__metric_env_get (atsopt_count_type arg0) {
ATSlocal(ats_ptr_type, tmp18) ;
ATSlocal(ats_ptr_type, tmp43) ;
ATSlocal(ats_ptr_type, tmp44) ;
ATSlocal(ats_ptr_type, tmp45) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__metric_env_get:
tmp43 = atspre_ref_get_view_ptr (tmp14) ;
tmp44 = (tmp43) ;
tmp45 = *((ats_ptr_type*)tmp44) ;
tmp18 = aux2_5 (tmp45, arg0) ;
return tmp18 ;
} /* fun */

ats_bool_type
aux1_4 (ats_ptr_type arg0, atsopt_count_type arg1) {
ATSlocal(ats_bool_type, tmp19) ;
ATSlocal(ats_ptr_type, tmp21) ;
ATSlocal(ats_ptr_type, tmp22) ;
ATSlocal(ats_bool_type, tmp23) ;
ATSlocal(atsopt_count_type, tmp24) ;
ATSlocal(ats_ptr_type, tmp27) ;
ATSlocal(atsopt_count_type, tmp28) ;
__ats_lab_aux1_4:
do {
__ats_lab_2:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_3 ; }
tmp21 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0*)arg0)->atslab_0 ;
tmp22 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0*)arg0)->atslab_1 ;
tmp24 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2var_get_stamp (tmp21) ;
tmp23 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_stamp_2esats__eq_stamp_stamp (tmp24, arg1) ;
if (tmp23) {
tmp19 = ats_true_bool ;
} else {
tmp27 = tmp22 ;
tmp28 = arg1 ;
arg0 = tmp27 ;
arg1 = tmp28 ;
goto __ats_lab_aux1_4 ;
} /* if */
break ;

__ats_lab_3:
tmp19 = ats_false_bool ;
break ;

} while (0) ;
return tmp19 ;
} /* fun */

ats_ptr_type
aux2_5 (ats_ptr_type arg0, atsopt_count_type arg1) {
ATSlocal(ats_ptr_type, tmp30) ;
ATSlocal(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_2, tmp32) ;
ATSlocal(ats_ptr_type, tmp33) ;
ATSlocal(ats_bool_type, tmp34) ;
ATSlocal(ats_ptr_type, tmp35) ;
ATSlocal(ats_ptr_type, tmp37) ;
ATSlocal(ats_ptr_type, tmp39) ;
ATSlocal(ats_ptr_type, tmp40) ;
ATSlocal(atsopt_count_type, tmp41) ;
__ats_lab_aux2_5:
do {
__ats_lab_4:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_5 ; }
tmp32 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_3*)arg0)->atslab_0 ;
tmp33 = &(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_3*)arg0)->atslab_1) ;
tmp35 = (tmp32).atslab_0 ;
tmp34 = aux1_4 (tmp35, arg1) ;
if (tmp34) {
tmp37 = (tmp32).atslab_1 ;
tmp30 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4*)tmp30)->atslab_0 = tmp37 ;

} else {
tmp40 = *((ats_ptr_type*)tmp33) ;
tmp39 = tmp40 ;
tmp41 = arg1 ;
arg0 = tmp39 ;
arg1 = tmp41 ;
goto __ats_lab_aux2_5 ;
} /* if */
break ;

__ats_lab_5:
tmp30 = (ats_sum_ptr_type)0 ;

break ;

} while (0) ;
return tmp30 ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__metric_env_pop () {
ATSlocal_void(tmp46) ;
ATSlocal(ats_int_type, tmp47) ;
ATSlocal(ats_ptr_type, tmp49) ;
ATSlocal(ats_ptr_type, tmp50) ;
ATSlocal(ats_ptr_type, tmp51) ;
ATSlocal(ats_ptr_type, tmp53) ;
ATSlocal(ats_bool_type, tmp55) ;
ATSlocal_void(tmp57) ;
ATSlocal_void(tmp58) ;
ATSlocal_void(tmp59) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__metric_env_pop:
tmp47 = 0 ;
tmp49 = atspre_ref_get_view_ptr (tmp14) ;
tmp50 = (tmp49) ;
tmp51 = *((ats_ptr_type*)tmp50) ;
do {
__ats_lab_6:
if (tmp51 == (ats_sum_ptr_type)0) { goto __ats_lab_7 ; }
tmp53 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_3*)tmp51)->atslab_1 ;
ATS_FREE(tmp51) ;
*((ats_ptr_type*)tmp50) = tmp53 ;
break ;

__ats_lab_7:
tmp47 = 1 ;
break ;

} while (0) ;
tmp55 = atspre_gt_int_int (tmp47, 0) ;
if (tmp55) {
/* tmp57 = */ atspre_prerr_string ("INTERNAL ERROR (ats_trans3_env_met)") ;
/* tmp58 = */ atspre_prerr_string (": metric_env_pop: the_metbindlst is empty.") ;
/* tmp59 = */ atspre_prerr_newline () ;
/* tmp46 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__abort () ;
} else {
} /* if */
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__metric_env_push (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp61) ;
ATSlocal(ats_ptr_type, tmp62) ;
ATSlocal(ats_ptr_type, tmp63) ;
ATSlocal(ats_ptr_type, tmp65) ;
ATSlocal(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_2, tmp66) ;
ATSlocal(ats_ptr_type, tmp67) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__metric_env_push:
tmp62 = atspre_ref_get_view_ptr (tmp14) ;
tmp63 = (tmp62) ;
tmp66.atslab_0 = arg0 ;
tmp66.atslab_1 = arg1 ;

tmp67 = *((ats_ptr_type*)tmp63) ;
tmp65 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_3)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_3*)tmp65)->atslab_0 = tmp66 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_3*)tmp65)->atslab_1 = tmp67 ;

*((ats_ptr_type*)tmp63) = tmp65 ;
/* tmp61 = ?void */ ;
return ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__s2exp_metfn_load (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_ptr_type, tmp68) ;
ATSlocal(ats_ptr_type, tmp109) ;
ATSlocal(ats_ptr_type, tmp110) ;
ATSlocal(ats_ptr_type, tmp112) ;
ATSlocal(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_2, tmp113) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__s2exp_metfn_load:
tmp109 = (ats_sum_ptr_type)0 ;

tmp110 = aux_9 (arg1, arg0, (&tmp109)) ;
do {
__ats_lab_18:
if (tmp110 == (ats_sum_ptr_type)0) { goto __ats_lab_19 ; }
tmp112 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4*)tmp110)->atslab_0 ;
ATS_FREE(tmp110) ;
tmp113.atslab_0 = tmp112 ;
tmp113.atslab_1 = tmp109 ;

tmp68 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_8)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_8*)tmp68)->atslab_0 = tmp113 ;

break ;

__ats_lab_19:
tmp68 = (ats_sum_ptr_type)0 ;

break ;

} while (0) ;
return tmp68 ;
} /* fun */

ats_ptr_type
aux_9 (ats_ptr_type env0, ats_ptr_type arg0, ats_ref_type arg1) {
ATSlocal(ats_ptr_type, tmp69) ;
ATSlocal(ats_ptr_type, tmp70) ;
ATSlocal(ats_ptr_type, tmp72) ;
ATSlocal(ats_int_type, tmp73) ;
ATSlocal(ats_ptr_type, tmp74) ;
ATSlocal(ats_int_type, tmp75) ;
ATSlocal(ats_ptr_type, tmp76) ;
ATSlocal(ats_ptr_type, tmp77) ;
ATSlocal(ats_ptr_type, tmp78) ;
ATSlocal(ats_ptr_type, tmp80) ;
ATSlocal(ats_ptr_type, tmp81) ;
ATSlocal(ats_ptr_type, tmp82) ;
ATSlocal(ats_ptr_type, tmp85) ;
ATSlocal(ats_ptr_type, tmp86) ;
ATSlocal(ats_ptr_type, tmp95) ;
ATSlocal(ats_ptr_type, tmp96) ;
ATSlocal(ats_ptr_type, tmp97) ;
ATSlocal(atsopt_count_type, tmp98) ;
ATSlocal(ats_ptr_type, tmp100) ;
ATSlocal(ats_ptr_type, tmp101) ;
ATSlocal(ats_ptr_type, tmp102) ;
ATSlocal(ats_ptr_type, tmp103) ;
ATSlocal(ats_ptr_type, tmp105) ;
ATSlocal(ats_ptr_type, tmp106) ;
__ats_lab_aux_9:
tmp70 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_1*)arg0)->atslab_s2exp_node ;
do {
__ats_lab_8:
if (((ats_sum_ptr_type)tmp70)->tag != 11) { goto __ats_lab_9 ; }
tmp72 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_5*)tmp70)->atslab_0 ;
tmp73 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_5*)tmp70)->atslab_1 ;
tmp74 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_5*)tmp70)->atslab_2 ;
tmp75 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_5*)tmp70)->atslab_3 ;
tmp76 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_5*)tmp70)->atslab_4 ;
tmp77 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_5*)tmp70)->atslab_5 ;
tmp78 = aux_9 (env0, tmp77, arg1) ;
do {
__ats_lab_10:
if (tmp78 == (ats_sum_ptr_type)0) { goto __ats_lab_11 ; }
tmp80 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4*)tmp78)->atslab_0 ;
ATS_FREE(tmp78) ;
tmp82 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_1*)arg0)->atslab_s2exp_srt ;
tmp81 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__s2exp_fun_srt (tmp82, tmp72, tmp73, tmp74, tmp75, tmp76, tmp80) ;
tmp69 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4*)tmp69)->atslab_0 = tmp81 ;

break ;

__ats_lab_11:
tmp69 = (ats_sum_ptr_type)0 ;

break ;

} while (0) ;
break ;

__ats_lab_9:
if (((ats_sum_ptr_type)tmp70)->tag != 15) { goto __ats_lab_12 ; }
tmp85 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_6*)tmp70)->atslab_1 ;
tmp86 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_6*)tmp70)->atslab_2 ;
tmp95 = aux_10 (tmp85) ;
*((ats_ptr_type*)arg1) = tmp95 ;
tmp98 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2var_get_stamp (env0) ;
tmp97 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_7)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_7*)tmp97)->atslab_0 = tmp98 ;

tmp96 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__s2exp_metfn (tmp97, tmp85, tmp86) ;
tmp69 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4*)tmp69)->atslab_0 = tmp96 ;

break ;

__ats_lab_12:
if (((ats_sum_ptr_type)tmp70)->tag != 30) { goto __ats_lab_15 ; }
tmp100 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_6*)tmp70)->atslab_0 ;
tmp101 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_6*)tmp70)->atslab_1 ;
tmp102 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_6*)tmp70)->atslab_2 ;
tmp103 = aux_9 (env0, tmp102, arg1) ;
do {
__ats_lab_16:
if (tmp103 == (ats_sum_ptr_type)0) { goto __ats_lab_17 ; }
tmp105 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4*)tmp103)->atslab_0 ;
ATS_FREE(tmp103) ;
tmp106 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__s2exp_uni (tmp100, tmp101, tmp105) ;
tmp69 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_4*)tmp69)->atslab_0 = tmp106 ;

break ;

__ats_lab_17:
tmp69 = (ats_sum_ptr_type)0 ;

break ;

} while (0) ;
break ;

__ats_lab_15:
tmp69 = (ats_sum_ptr_type)0 ;

break ;

} while (0) ;
return tmp69 ;
} /* fun */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_ptr_type closure_env_0 ;
} aux_9_clo_type ;

ats_clo_ptr_type
aux_9_clo_make (ats_ptr_type env0) {
aux_9_clo_type *p = ATS_MALLOC(sizeof(aux_9_clo_type)) ;
p->closure_fun = (ats_fun_ptr_type)&aux_9_clofun ;
p->closure_env_0 = env0 ;
return (ats_clo_ptr_type)p ;
}

ats_ptr_type
aux_9_clofun (ats_clo_ptr_type clo, ats_ptr_type arg0, ats_ref_type arg1) {
return aux_9 (((aux_9_clo_type *)clo)->closure_env_0, arg0, arg1) ;
}

ats_ptr_type
aux_10 (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp88) ;
ATSlocal(ats_ptr_type, tmp90) ;
ATSlocal(ats_ptr_type, tmp91) ;
ATSlocal(ats_ptr_type, tmp92) ;
ATSlocal(ats_ptr_type, tmp93) ;
__ats_lab_aux_10:
do {
__ats_lab_13:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_14 ; }
tmp90 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0*)arg0)->atslab_0 ;
tmp91 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0*)arg0)->atslab_1 ;
tmp92 = ((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_rec_1*)tmp90)->atslab_s2exp_srt ;
tmp93 = aux_10 (tmp91) ;
tmp88 = ATS_MALLOC(sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0)) ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0*)tmp88)->atslab_0 = tmp92 ;
((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats_sum_0*)tmp88)->atslab_1 = tmp93 ;

break ;

__ats_lab_14:
tmp88 = (ats_sum_ptr_type)0 ;

break ;

} while (0) ;
return tmp88 ;
} /* fun */

/* static load function */

extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2edats__staload () ;
static int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats__staload_flag = 0 ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats__staload () {
if (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats__staload_flag) return ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats__staload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2edats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__FatalErrorException.tag = ats_exception_con_tag_new () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__FatalErrorException.name = "_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__FatalErrorException" ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__DeadCodeException.tag = ats_exception_con_tag_new () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__DeadCodeException.name = "_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_error_2esats__DeadCodeException" ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibats_lex_lexing_2esats__LexingErrorException.tag = ats_exception_con_tag_new () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibats_lex_lexing_2esats__LexingErrorException.name = "_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibats_lex_lexing_2esats__LexingErrorException" ;
}

/* dynamic load function */

extern int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats__dynload_flag ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats__dynload () {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats__dynload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_trans3_env_met_2edats__staload () ;
ats_gc_markroot(&tmp14, sizeof(ats_ptr_type)) ;
ats_gc_markroot(&tmp17, sizeof(ats_ptr_type)) ;
tmp17 = (ats_sum_ptr_type)0 ;

tmp14 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_reference_2esats__ref_make_elt__ats_ptr_type (tmp17) ;
}

/* external types */

/* external codes at mid */

/* external codes at bot */

