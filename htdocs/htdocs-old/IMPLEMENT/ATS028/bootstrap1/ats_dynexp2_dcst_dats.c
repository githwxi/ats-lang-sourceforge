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
ats_ptr_type atslab_d2cst_sym ;
ats_ptr_type atslab_d2cst_fil ;
ats_ptr_type atslab_d2cst_loc ;
ats_ptr_type atslab_d2cst_kind ;
ats_ptr_type atslab_d2cst_decarg ;
ats_ptr_type atslab_d2cst_arilst ;
ats_ptr_type atslab_d2cst_typ ;
ats_ptr_type atslab_d2cst_extdef ;
ats_ptr_type atslab_d2cst_def ;
atsopt_count_type atslab_d2cst_stamp ;
ats_ptr_type atslab_d2cst_hityp ;
} _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0 ;

/* external dynamic constructor declarations */

ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__list_cons) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__list_nil) ;
ATSextern(ats_sum_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fprelude_2fGEIZELLA_2fbasics_sta_2esats__None) ;

/* external dynamic constant declarations */

extern ats_void_type atspre_vbox_make_view_ptr(ats_ptr_type) ;
extern ats_ptr_type atspre_stdout_get() ;
extern ats_void_type atspre_stdout_view_set() ;
extern ats_ptr_type atspre_stderr_get() ;
extern ats_void_type atspre_stderr_view_set() ;
extern ats_bool_type atspre_ilt(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_ilte(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_ieq(ats_int_type, ats_int_type) ;
extern ats_bool_type atspre_ineq(ats_int_type, ats_int_type) ;
extern ats_ptr_type atspre_ptr_alloc_tsz(ats_size_type) ;
extern ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_list_2esats__fprintlst(ats_ref_type, ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
extern ats_int_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_stamp_2esats__compare_stamp_stamp(atsopt_count_type, atsopt_count_type) ;
extern atsopt_count_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_stamp_2esats__d2cst_stamp_make() ;
extern ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__fprint_symbol(ats_ref_type, ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_fun(ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_castfn(ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_praxi(ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_prfun(ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_prval(ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_proof(ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstextdef_is_mac(ats_ptr_type) ;
extern ats_bool_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstextdef_is_sta(ats_ptr_type) ;
extern ats_ptr_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_sym(ats_ptr_type) ;
extern ats_int_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__compare_d2cst_d2cst(ats_ptr_type, ats_ptr_type) ;
extern ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cst(ats_ref_type, ats_ptr_type) ;
extern ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cstlst(ats_ref_type, ats_ptr_type) ;

/* internal function declarations */

static ats_int_type _compare_d2cst_d2cst_18 (ats_ptr_type arg0, ats_ptr_type arg1) ;

/* sum constructor declarations */

/* exception constructor declarations */

ATSglobal(ats_exn_type, _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibats_lex_lexing_2esats__LexingErrorException) ;

/* global dynamic constant declarations */

/* static temporary variable declarations */

/* function implementations */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_make (ats_ptr_type arg0, ats_ptr_type arg1, ats_ptr_type arg2, ats_ptr_type arg3, ats_ptr_type arg4, ats_ptr_type arg5, ats_ptr_type arg6, ats_ptr_type arg7) {
ATSlocal(ats_ptr_type, tmp0) ;
ATSlocal(atsopt_count_type, tmp1) ;
ATSlocal(ats_ptr_type, tmp2) ;
ATSlocal(ats_ptr_type, tmp3) ;
ATSlocal(ats_ptr_type, tmp14) ;
ATSlocal(ats_ptr_type, tmp17) ;
ATSlocal_void(tmp18) ;
ATSlocal_void(tmp19) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_make:
tmp1 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_stamp_2esats__d2cst_stamp_make () ;
tmp2 = atspre_ptr_alloc_tsz (sizeof(_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0)) ;
tmp3 = (tmp2) ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_sym) = arg0 ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_fil) = arg1 ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_loc) = arg2 ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_kind) = arg3 ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_decarg) = arg4 ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_arilst) = arg5 ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_typ) = arg6 ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_extdef) = arg7 ;
tmp14 = (ats_sum_ptr_type)0 ;

(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_def) = tmp14 ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_stamp) = tmp1 ;
tmp17 = (ats_sum_ptr_type)0 ;

(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp3)->atslab_d2cst_hityp) = tmp17 ;
/* tmp18 = */ atspre_vbox_make_view_ptr (tmp3) ;
/* tmp19 = (tmp18) */;
tmp0 = tmp3 ;
return tmp0 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_sym (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp20) ;
ATSlocal(ats_ptr_type, tmp21) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_sym:
tmp21 = (arg0) ;
tmp20 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp21)->atslab_d2cst_sym) ;
return tmp20 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_loc (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp22) ;
ATSlocal(ats_ptr_type, tmp23) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_loc:
tmp23 = (arg0) ;
tmp22 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp23)->atslab_d2cst_loc) ;
return tmp22 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_fil (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp24) ;
ATSlocal(ats_ptr_type, tmp25) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_fil:
tmp25 = (arg0) ;
tmp24 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp25)->atslab_d2cst_fil) ;
return tmp24 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_kind (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp26) ;
ATSlocal(ats_ptr_type, tmp27) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_kind:
tmp27 = (arg0) ;
tmp26 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp27)->atslab_d2cst_kind) ;
return tmp26 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_arilst (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp28) ;
ATSlocal(ats_ptr_type, tmp29) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_arilst:
tmp29 = (arg0) ;
tmp28 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp29)->atslab_d2cst_arilst) ;
return tmp28 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_decarg (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp30) ;
ATSlocal(ats_ptr_type, tmp31) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_decarg:
tmp31 = (arg0) ;
tmp30 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp31)->atslab_d2cst_decarg) ;
return tmp30 ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_set_decarg (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp32) ;
ATSlocal(ats_ptr_type, tmp33) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_set_decarg:
tmp33 = (arg0) ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp33)->atslab_d2cst_decarg) = arg1 ;
return ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_typ (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp34) ;
ATSlocal(ats_ptr_type, tmp35) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_typ:
tmp35 = (arg0) ;
tmp34 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp35)->atslab_d2cst_typ) ;
return tmp34 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_extdef (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp36) ;
ATSlocal(ats_ptr_type, tmp37) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_extdef:
tmp37 = (arg0) ;
tmp36 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp37)->atslab_d2cst_extdef) ;
return tmp36 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_def (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp38) ;
ATSlocal(ats_ptr_type, tmp39) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_def:
tmp39 = (arg0) ;
tmp38 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp39)->atslab_d2cst_def) ;
return tmp38 ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_set_def (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp40) ;
ATSlocal(ats_ptr_type, tmp41) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_set_def:
tmp41 = (arg0) ;
(((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp41)->atslab_d2cst_def) = arg1 ;
return ;
} /* fun */

atsopt_count_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_stamp (ats_ptr_type arg0) {
ATSlocal(atsopt_count_type, tmp42) ;
ATSlocal(ats_ptr_type, tmp43) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_stamp:
tmp43 = (arg0) ;
tmp42 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp43)->atslab_d2cst_stamp) ;
return tmp42 ;
} /* fun */

ats_ptr_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_hiexp_2esats__d2cst_get_hityp (ats_ptr_type arg0) {
ATSlocal(ats_ptr_type, tmp44) ;
ATSlocal(ats_ptr_type, tmp45) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_hiexp_2esats__d2cst_get_hityp:
tmp45 = (arg0) ;
tmp44 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp45)->atslab_d2cst_hityp) ;
return tmp44 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__lt_d2cst_d2cst (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp46) ;
ATSlocal(ats_int_type, tmp47) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__lt_d2cst_d2cst:
tmp47 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__compare_d2cst_d2cst (arg0, arg1) ;
tmp46 = atspre_ilt (tmp47, 0) ;
return tmp46 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__lte_d2cst_d2cst (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp48) ;
ATSlocal(ats_int_type, tmp49) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__lte_d2cst_d2cst:
tmp49 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__compare_d2cst_d2cst (arg0, arg1) ;
tmp48 = atspre_ilte (tmp49, 0) ;
return tmp48 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__eq_d2cst_d2cst (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp50) ;
ATSlocal(ats_int_type, tmp51) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__eq_d2cst_d2cst:
tmp51 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__compare_d2cst_d2cst (arg0, arg1) ;
tmp50 = atspre_ieq (tmp51, 0) ;
return tmp50 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__neq_d2cst_d2cst (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_bool_type, tmp52) ;
ATSlocal(ats_int_type, tmp53) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__neq_d2cst_d2cst:
tmp53 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__compare_d2cst_d2cst (arg0, arg1) ;
tmp52 = atspre_ineq (tmp53, 0) ;
return tmp52 ;
} /* fun */

ats_int_type
_compare_d2cst_d2cst_18 (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_int_type, tmp54) ;
ATSlocal(atsopt_count_type, tmp55) ;
ATSlocal(ats_ptr_type, tmp56) ;
ATSlocal(atsopt_count_type, tmp57) ;
ATSlocal(ats_ptr_type, tmp58) ;
__ats_lab__compare_d2cst_d2cst_18:
tmp56 = (arg0) ;
tmp55 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp56)->atslab_d2cst_stamp) ;
tmp58 = (arg1) ;
tmp57 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp58)->atslab_d2cst_stamp) ;
tmp54 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_stamp_2esats__compare_stamp_stamp (tmp55, tmp57) ;
return tmp54 ;
} /* fun */

ats_int_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__compare_d2cst_d2cst (ats_ptr_type arg0, ats_ptr_type arg1) {
ATSlocal(ats_int_type, tmp59) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__compare_d2cst_d2cst:
tmp59 = _compare_d2cst_d2cst_18 (arg0, arg1) ;
return tmp59 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_fun (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp60) ;
ATSlocal(ats_ptr_type, tmp61) ;
ATSlocal(ats_ptr_type, tmp62) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_fun:
tmp62 = (arg0) ;
tmp61 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp62)->atslab_d2cst_kind) ;
tmp60 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_fun (tmp61) ;
return tmp60 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_extmac (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp63) ;
ATSlocal(ats_ptr_type, tmp64) ;
ATSlocal(ats_ptr_type, tmp65) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_extmac:
tmp65 = (arg0) ;
tmp64 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp65)->atslab_d2cst_extdef) ;
tmp63 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstextdef_is_mac (tmp64) ;
return tmp63 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_extsta (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp66) ;
ATSlocal(ats_ptr_type, tmp67) ;
ATSlocal(ats_ptr_type, tmp68) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_extsta:
tmp68 = (arg0) ;
tmp67 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp68)->atslab_d2cst_extdef) ;
tmp66 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstextdef_is_sta (tmp67) ;
return tmp66 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_castfn (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp69) ;
ATSlocal(ats_ptr_type, tmp70) ;
ATSlocal(ats_ptr_type, tmp71) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_castfn:
tmp71 = (arg0) ;
tmp70 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp71)->atslab_d2cst_kind) ;
tmp69 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_castfn (tmp70) ;
return tmp69 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_praxi (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp72) ;
ATSlocal(ats_ptr_type, tmp73) ;
ATSlocal(ats_ptr_type, tmp74) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_praxi:
tmp74 = (arg0) ;
tmp73 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp74)->atslab_d2cst_kind) ;
tmp72 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_praxi (tmp73) ;
return tmp72 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_prfun (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp75) ;
ATSlocal(ats_ptr_type, tmp76) ;
ATSlocal(ats_ptr_type, tmp77) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_prfun:
tmp77 = (arg0) ;
tmp76 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp77)->atslab_d2cst_kind) ;
tmp75 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_prfun (tmp76) ;
return tmp75 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_prval (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp78) ;
ATSlocal(ats_ptr_type, tmp79) ;
ATSlocal(ats_ptr_type, tmp80) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_prval:
tmp80 = (arg0) ;
tmp79 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp80)->atslab_d2cst_kind) ;
tmp78 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_prval (tmp79) ;
return tmp78 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_proof (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp81) ;
ATSlocal(ats_ptr_type, tmp82) ;
ATSlocal(ats_ptr_type, tmp83) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_proof:
tmp83 = (arg0) ;
tmp82 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp83)->atslab_d2cst_kind) ;
tmp81 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__dcstkind_is_proof (tmp82) ;
return tmp81 ;
} /* fun */

ats_bool_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_temp (ats_ptr_type arg0) {
ATSlocal(ats_bool_type, tmp84) ;
ATSlocal(ats_ptr_type, tmp85) ;
ATSlocal(ats_ptr_type, tmp86) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_is_temp:
tmp86 = (arg0) ;
tmp85 = (((_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0*)tmp86)->atslab_d2cst_decarg) ;
do {
__ats_lab_0:
if (tmp85 == (ats_sum_ptr_type)0) { goto __ats_lab_1 ; }
tmp84 = ats_true_bool ;
break ;

__ats_lab_1:
tmp84 = ats_false_bool ;
break ;

} while (0) ;
return tmp84 ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cst (ats_ref_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp89) ;
ATSlocal(ats_ptr_type, tmp90) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cst:
tmp90 = _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__d2cst_get_sym (arg1) ;
/* tmp89 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_symbol_2esats__fprint_symbol (arg0, tmp90) ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__print_d2cst (ats_ptr_type arg0) {
ATSlocal_void(tmp91) ;
ATSlocal(ats_ptr_type, tmp92) ;
ATSlocal(ats_ptr_type, tmp93) ;
ATSlocal_void(tmp94) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__print_d2cst:
tmp92 = atspre_stdout_get () ;
tmp93 = (tmp92) ;
/* tmp94 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cst (tmp93, arg0) ;
/* tmp91 = */ atspre_stdout_view_set () ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__prerr_d2cst (ats_ptr_type arg0) {
ATSlocal_void(tmp95) ;
ATSlocal(ats_ptr_type, tmp96) ;
ATSlocal(ats_ptr_type, tmp97) ;
ATSlocal_void(tmp98) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__prerr_d2cst:
tmp96 = atspre_stderr_get () ;
tmp97 = (tmp96) ;
/* tmp98 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cst (tmp97, arg0) ;
/* tmp95 = */ atspre_stderr_view_set () ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cstlst (ats_ref_type arg0, ats_ptr_type arg1) {
ATSlocal_void(tmp99) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cstlst:
/* tmp99 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_list_2esats__fprintlst (arg0, arg1, ", ", &_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cst) ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__print_d2cstlst (ats_ptr_type arg0) {
ATSlocal_void(tmp100) ;
ATSlocal(ats_ptr_type, tmp101) ;
ATSlocal(ats_ptr_type, tmp102) ;
ATSlocal_void(tmp103) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__print_d2cstlst:
tmp101 = atspre_stdout_get () ;
tmp102 = (tmp101) ;
/* tmp103 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cstlst (tmp102, arg0) ;
/* tmp100 = */ atspre_stdout_view_set () ;
return ;
} /* fun */

ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__prerr_d2cstlst (ats_ptr_type arg0) {
ATSlocal_void(tmp104) ;
ATSlocal(ats_ptr_type, tmp105) ;
ATSlocal(ats_ptr_type, tmp106) ;
ATSlocal_void(tmp107) ;
__ats_lab__2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__prerr_d2cstlst:
tmp105 = atspre_stderr_get () ;
tmp106 = (tmp105) ;
/* tmp107 = */ _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__fprint_d2cstlst (tmp106, arg0) ;
/* tmp104 = */ atspre_stderr_view_set () ;
return ;
} /* fun */

/* static load function */

extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_list_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_stamp_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_hiexp_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__staload () ;
extern ats_void_type
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__staload () ;
static int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats__staload_flag = 0 ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats__staload () {
if (_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats__staload_flag) return ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats__staload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_list_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_stamp_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_syntax_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_hiexp_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_staexp2_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_2esats__staload () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibats_lex_lexing_2esats__LexingErrorException.tag = ats_exception_con_tag_new () ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibats_lex_lexing_2esats__LexingErrorException.name = "_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2flibats_lex_lexing_2esats__LexingErrorException" ;
}

/* dynamic load function */

extern int _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats__dynload_flag ;
ats_void_type _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats__dynload () {
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats__dynload_flag = 1 ;
_2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats__staload () ;
}

/* external types */

typedef _2fhome_2ffac2_2fhwxi_2fresearch_2fATS_2fIMPLEMENT_2fGeizella_2fAnairiats_2fsvn_2fats_2dlang_2fsrc_2fats_dynexp2_dcst_2edats_rec_0 d2cst_struct ;

/* external codes at mid */

/* external codes at bot */



ats_void_type
atsopt_d2cst_set_hityp (
  ats_ptr_type d2c, ats_ptr_type ohit
) {
  ((d2cst_struct*)d2c)->atslab_d2cst_hityp = ohit ; return ;
} /* end of [atsopt_d2cst_set_hityp] */


