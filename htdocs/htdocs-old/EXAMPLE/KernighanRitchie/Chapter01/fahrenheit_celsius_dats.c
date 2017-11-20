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
/* type definitions */
/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
extern
ats_double_type atspre_double_of_int (ats_int_type) ;
extern
ats_double_type atspre_mul_double_double (ats_double_type, ats_double_type) ;
extern
ats_double_type atspre_div_double_double (ats_double_type, ats_double_type) ;
extern
ats_int_type atspre_add_int_int (ats_int_type, ats_int_type) ;
extern
ats_int_type atspre_sub_int_int (ats_int_type, ats_int_type) ;
extern
ats_bool_type atspre_lte_int_int (ats_int_type, ats_int_type) ;
extern
ats_void_type atspre_printf_exn (ats_ptr_type, ...) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_TERMINATION_CHECK
#endif /* _ATS_TERMINATION_CHECK */

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_void_type loop_1 (ats_int_type arg0) ;

/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/fac2/hwxi/research/ATS/IMPLEMENT/Geizella/Anairiats/svn/ats-lang/doc/EXAMPLE/KernighanRitchie/Chapter01/fahrenheit_celsius.dats: 436(line=28, offs=7) -- 612(line=33, offs=8)
*/
ats_void_type
loop_1 (ats_int_type arg0) {
/* local vardec */
ATSlocal_void (tmp1) ;
ATSlocal (ats_bool_type, tmp2) ;
ATSlocal_void (tmp3) ;
ATSlocal (ats_double_type, tmp4) ;
ATSlocal (ats_double_type, tmp5) ;
ATSlocal (ats_double_type, tmp6) ;
ATSlocal (ats_int_type, tmp7) ;
ATSlocal (ats_int_type, tmp8) ;

__ats_lab_loop_1:
tmp2 = atspre_lte_int_int (arg0, 300) ;
if (tmp2) {
tmp5 = atspre_div_double_double (5.0, 9.0) ;
tmp7 = atspre_sub_int_int (arg0, 32) ;
tmp6 = atspre_double_of_int (tmp7) ;
tmp4 = atspre_mul_double_double (tmp5, tmp6) ;
/* tmp3 = */ atspre_printf_exn ((ats_ptr_type)"%3d %6.1f\n", arg0, tmp4) ;
tmp8 = atspre_add_int_int (arg0, 20) ;
arg0 = tmp8 ;
goto __ats_lab_loop_1 ; // tail call
} else {
/* empty */
} /* end of [if] */
return /* (tmp1) */ ;
} /* end of [loop_1] */

/*
// /home/fac2/hwxi/research/ATS/IMPLEMENT/Geizella/Anairiats/svn/ats-lang/doc/EXAMPLE/KernighanRitchie/Chapter01/fahrenheit_celsius.dats: 404(line=27, offs=16) -- 631(line=34, offs=2)
*/
ats_void_type
mainats () {
/* local vardec */
ATSlocal_void (tmp0) ;

__ats_lab_mainats:
/* tmp0 = */ loop_1 (0) ;
return /* (tmp0) */ ;
} /* end of [mainats] */

/* static load function */

static int ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2fahrenheit_celsius_2edats__staload_flag = 0 ;

ats_void_type
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2fahrenheit_celsius_2edats__staload () {
if (ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2fahrenheit_celsius_2edats__staload_flag) return ;
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2fahrenheit_celsius_2edats__staload_flag = 1 ;
return ;
} /* staload function */
/* dynamic load function */

// (external) dynload flag declaration
// extern
// int ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2fahrenheit_celsius_2edats__dynload_flag ;

ats_void_type
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2fahrenheit_celsius_2edats__dynload () {
// ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2fahrenheit_celsius_2edats__dynload_flag = 1 ;
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2fahrenheit_celsius_2edats__staload () ;
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
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2fahrenheit_celsius_2edats__dynload() ;
mainats((ats_int_type)argc, (ats_ptr_type)argv) ;
return (0) ;
} /* end of main */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [fahrenheit_celsius_dats.c] */
