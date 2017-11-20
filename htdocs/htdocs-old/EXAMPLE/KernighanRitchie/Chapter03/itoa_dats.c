/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2010-3-8: 20h:54m
**
*/

/* include some .h files */
#ifndef _ATS_HEADER_NONE
#include "ats_types.h"
#include "ats_basics.h"
#include "ats_exception.h"
#include "ats_memory.h"
#endif /* _ATS_HEADER_NONE */

/* include some .cats files */
#ifndef _ATS_PRELUDE_NONE
#include "prelude/CATS/array.cats"
#include "prelude/CATS/basics.cats"
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/integer_fixed.cats"
#include "prelude/CATS/integer_ptr.cats"
#include "prelude/CATS/lazy.cats"
#include "prelude/CATS/lazy_vt.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/printf.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/sizetype.cats"
#include "prelude/CATS/string.cats"
#include "prelude/CATS/array.cats"
#include "prelude/CATS/list.cats"
#include "prelude/CATS/option.cats"
#include "prelude/CATS/slseg.cats"
#endif /* _ATS_PRELUDE_NONE */
/* prologue from statically loaded files */
/* external codes at top */


ats_char_type char_of_digit (ats_int_type i) { return (i + '0') ; }



ats_void_type strbuf_reverse (ats_ptr_type s0) {
  char *s = (char*)s0 ; int c, i, j ;
  for (i = 0, j = strlen(s) - 1; i < j; i++, j--) {
    c = s[i]; s[i] = s[j]; s[j] = c;
  }
  return ;
} /* end of [strbuf_reverse] */


/* type definitions */
/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
extern
ats_void_type atspre_assert (ats_bool_type) ;
extern
ats_void_type atspre_print_newline () ;
extern
ats_int_type atspre_int_of_string (ats_ptr_type) ;
extern
ats_int_type atspre_ineg (ats_int_type) ;
extern
ats_int_type atspre_iadd (ats_int_type, ats_int_type) ;
extern
ats_int_type atspre_idiv (ats_int_type, ats_int_type) ;
extern
ats_int_type atspre_nmod (ats_int_type, ats_int_type) ;
extern
ats_bool_type atspre_ilt (ats_int_type, ats_int_type) ;
extern
ats_bool_type atspre_igt (ats_int_type, ats_int_type) ;
extern
ats_bool_type atspre_igte (ats_int_type, ats_int_type) ;
extern
ats_bool_type atspre_ieq (ats_int_type, ats_int_type) ;
extern
ats_size_type atspre_size1_of_int1 (ats_int_type) ;
extern
ats_void_type atspre_bytes_strbuf_trans (ats_ptr_type, ats_size_type) ;
extern
ats_void_type atspre_print_string (ats_ptr_type) ;
extern
ats_int_type ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__itoa_err (ats_int_type, ats_ptr_type, ats_int_type) ;
extern
ats_char_type char_of_digit (ats_int_type) ;
extern
ats_void_type strbuf_reverse (ats_ref_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_TERMINATION_CHECK
#endif /* _ATS_TERMINATION_CHECK */

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_void_type loop_1 (ats_int_type arg0, ats_ref_type arg1, ats_int_type arg2, ats_ref_type arg3) ;

/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/fac2/hwxi/research/ATS/IMPLEMENT/Geizella/Anairiats/svn/ats-lang/doc/EXAMPLE/KernighanRitchie/Chapter03/itoa.dats: 1395(line=69, offs=7) -- 1739(line=81, offs=8)
*/
ats_void_type
loop_1 (ats_int_type arg0, ats_ref_type arg1, ats_int_type arg2, ats_ref_type arg3) {
/* local vardec */
ATSlocal_void (tmp1) ;
ATSlocal (ats_bool_type, tmp2) ;
ATSlocal (ats_bool_type, tmp3) ;
ATSlocal (ats_int_type, tmp4) ;
ATSlocal (ats_char_type, tmp5) ;
ATSlocal (ats_int_type, tmp6) ;
ATSlocal (ats_int_type, tmp7) ;

__ats_lab_loop_1:
tmp2 = atspre_ilt (*((ats_int_type*)arg3), arg2) ;
if (tmp2) {
tmp3 = atspre_igt (arg0, 0) ;
if (tmp3) {
tmp4 = atspre_nmod (arg0, 10) ;
tmp5 = char_of_digit (tmp4) ;
((ats_char_type*)arg1)[*((ats_int_type*)arg3)] = tmp5 ;
tmp6 = atspre_iadd (*((ats_int_type*)arg3), 1) ;
*((ats_int_type*)arg3) = tmp6 ;
tmp7 = atspre_idiv (arg0, 10) ;
arg0 = tmp7 ;
arg1 = arg1 ;
arg2 = arg2 ;
arg3 = arg3 ;
goto __ats_lab_loop_1 ; // tail call
} else {
/* empty */
} /* end of [if] */
} else {
/* empty */
} /* end of [if] */
return /* (tmp1) */ ;
} /* end of [loop_1] */

/*
// /home/fac2/hwxi/research/ATS/IMPLEMENT/Geizella/Anairiats/svn/ats-lang/doc/EXAMPLE/KernighanRitchie/Chapter03/itoa.dats: 1358(line=68, offs=30) -- 2457(line=104, offs=4)
*/
ats_int_type
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__itoa_err (ats_int_type arg0, ats_ptr_type arg1, ats_int_type arg2) {
/* local vardec */
ATSlocal (ats_int_type, tmp0) ;
ATSlocal (ats_int_type, tmp8) ;
ATSlocal (ats_int_type, tmp9) ;
ATSlocal (ats_bool_type, tmp10) ;
ATSlocal_void (tmp11) ;
ATSlocal (ats_bool_type, tmp13) ;
ATSlocal (ats_bool_type, tmp15) ;
ATSlocal (ats_bool_type, tmp16) ;
ATSlocal (ats_int_type, tmp17) ;
ATSlocal (ats_bool_type, tmp18) ;
ATSlocal_void (tmp19) ;
ATSlocal (ats_size_type, tmp20) ;
ATSlocal_void (tmp21) ;

__ats_lab_ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__itoa_err:
/* ats_int_type tmp8 ; */
tmp8 = 0 ;
tmp10 = atspre_igte (ats_castfn_mac(ats_int_type, arg0), 0) ;
if (tmp10) {
tmp9 = ats_castfn_mac(ats_int_type, arg0) ;
} else {
tmp9 = atspre_ineg (ats_castfn_mac(ats_int_type, arg0)) ;
} /* end of [if] */
/* tmp11 = */ loop_1 (tmp9, arg1, arg2, (&tmp8)) ;
tmp13 = atspre_ieq (tmp8, 0) ;
if (tmp13) {
((ats_char_type*)arg1)[0] = '0' ;
tmp8 = 1 ;
} else {
/* empty */
} /* end of [if] */
tmp15 = atspre_ilt (ats_castfn_mac(ats_int_type, arg0), 0) ;
if (tmp15) {
tmp16 = atspre_ilt (tmp8, arg2) ;
if (tmp16) {
((ats_char_type*)arg1)[tmp8] = '-' ;
tmp17 = atspre_iadd (tmp8, 1) ;
tmp8 = tmp17 ;
} else {
/* empty */
} /* end of [if] */
} else {
/* empty */
} /* end of [if] */
tmp18 = atspre_ilt (tmp8, arg2) ;
if (tmp18) {
tmp20 = atspre_size1_of_int1 (tmp8) ;
/* tmp19 = */ atspre_bytes_strbuf_trans (arg1, tmp20) ;
/* tmp21 = */ strbuf_reverse (arg1) ;
tmp0 = 0 ;
} else {
tmp0 = -1 ;
} /* end of [if] */
return (tmp0) ;
} /* end of [ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__itoa_err] */

/*
// /home/fac2/hwxi/research/ATS/IMPLEMENT/Geizella/Anairiats/svn/ats-lang/doc/EXAMPLE/KernighanRitchie/Chapter03/itoa.dats: 2516(line=108, offs=16) -- 3196(line=131, offs=4)
*/
ats_void_type
mainats (ats_int_type arg0, ats_ref_type arg1) {
/* local vardec */
ATSlocal_void (tmp22) ;
ATSlocal_void (tmp23) ;
ATSlocal (ats_bool_type, tmp24) ;
ATSlocal (ats_int_type, tmp25) ;
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_int_type, tmp28) ;
ATSlocal (ats_int_type, tmp29) ;
ATSlocal (ats_bool_type, tmp30) ;
ATSlocal_void (tmp31) ;
ATSlocal_void (tmp32) ;

__ats_lab_mainats:
tmp24 = atspre_igte (arg0, 2) ;
/* tmp23 = */ atspre_assert (tmp24) ;
tmp26 = ((ats_ptr_type*)arg1)[1] ;
tmp25 = atspre_int_of_string (tmp26) ;
/* ats_ptr_type tmp27 ; */
/* array allocation on stack */
tmp27 = ATS_ALLOCA2(16, sizeof(ats_byte_type)) ;
tmp28 = ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__itoa_err (tmp25, tmp27, 16) ;
tmp29 = (tmp28) ;
tmp30 = atspre_igte (tmp29, 0) ;
if (tmp30) {
/* tmp31 = */ atspre_print_string (ats_castfn_mac(ats_ptr_type, tmp27)) ;
/* tmp22 = */ atspre_print_newline () ;
} else {
/* tmp32 = */ atspre_print_string ((ats_ptr_type)"?") ;
/* tmp22 = */ atspre_print_newline () ;
} /* end of [if] */
return /* (tmp22) */ ;
} /* end of [mainats] */

/* static load function */

static int ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__staload_flag = 0 ;

ats_void_type
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__staload () {
if (ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__staload_flag) return ;
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__staload_flag = 1 ;
return ;
} /* staload function */
/* dynamic load function */

// (external) dynload flag declaration
// extern
// int ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__dynload_flag ;

ats_void_type
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__dynload () {
// ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__dynload_flag = 1 ;
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__staload () ;
#ifdef _ATS_TERMINATION_CHECK
#endif /* _ATS_TERMINATION_CHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

int main (int argc, char *argv[]) {
ATS_GC_INIT() ;
mainats_prelude() ;
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter03_2itoa_2edats__dynload() ;
mainats((ats_int_type)argc, (ats_ptr_type)argv) ;
return (0) ;
} /* end of main */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [itoa_dats.c] */