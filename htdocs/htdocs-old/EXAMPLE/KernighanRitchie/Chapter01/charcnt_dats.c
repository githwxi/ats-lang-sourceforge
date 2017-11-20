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

#include "libc/CATS/stdio.cats"


#include "libc/sys/CATS/types.cats"

/* external codes at top */
/* type definitions */
/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
extern
ats_double_type atspre_add_double_double (ats_double_type, ats_double_type) ;
extern
ats_bool_type atspre_neq_int_int (ats_int_type, ats_int_type) ;
extern
ats_void_type atspre_printf_exn (ats_ptr_type, ...) ;
extern
ats_int_type atslib_getchar () ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_TERMINATION_CHECK
#endif /* _ATS_TERMINATION_CHECK */

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_double_type loop_1 (ats_double_type arg0) ;

/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/fac2/hwxi/research/ATS/IMPLEMENT/Geizella/Anairiats/svn/ats-lang/doc/EXAMPLE/KernighanRitchie/Chapter01/charcnt.dats: 340(line=23, offs=9) -- 423(line=24, offs=56)
*/
ats_double_type
loop_1 (ats_double_type arg0) {
/* local vardec */
ATSlocal (ats_double_type, tmp1) ;
ATSlocal (ats_bool_type, tmp2) ;
ATSlocal (ats_int_type, tmp3) ;
ATSlocal (ats_double_type, tmp4) ;

__ats_lab_loop_1:
tmp3 = atslib_getchar () ;
tmp2 = atspre_neq_int_int (tmp3, EOF) ;
if (tmp2) {
tmp4 = atspre_add_double_double (arg0, 1.0) ;
arg0 = tmp4 ;
goto __ats_lab_loop_1 ; // tail call
} else {
tmp1 = arg0 ;
} /* end of [if] */
return (tmp1) ;
} /* end of [loop_1] */

/*
// /home/fac2/hwxi/research/ATS/IMPLEMENT/Geizella/Anairiats/svn/ats-lang/doc/EXAMPLE/KernighanRitchie/Chapter01/charcnt.dats: 293(line=21, offs=16) -- 461(line=28, offs=4)
*/
ats_void_type
mainats () {
/* local vardec */
ATSlocal_void (tmp0) ;
ATSlocal (ats_double_type, tmp5) ;

__ats_lab_mainats:
tmp5 = loop_1 (0.0) ;
/* tmp0 = */ atspre_printf_exn ((ats_ptr_type)"%.0f\n", tmp5) ;
return /* (tmp0) */ ;
} /* end of [mainats] */

/* static load function */

extern
ats_void_type ATS_2d0_2e2_2e0_2libc_2SATS_2stdio_2esats__staload (void) ;
static int ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2charcnt_2edats__staload_flag = 0 ;

ats_void_type
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2charcnt_2edats__staload () {
if (ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2charcnt_2edats__staload_flag) return ;
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2charcnt_2edats__staload_flag = 1 ;
ATS_2d0_2e2_2e0_2libc_2SATS_2stdio_2esats__staload () ;
return ;
} /* staload function */
/* dynamic load function */

// (external) dynload flag declaration
// extern
// int ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2charcnt_2edats__dynload_flag ;

ats_void_type
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2charcnt_2edats__dynload () {
// ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2charcnt_2edats__dynload_flag = 1 ;
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2charcnt_2edats__staload () ;
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
ATS_2d0_2e2_2e0_2doc_2EXAMPLE_2KernighanRitchie_2Chapter01_2charcnt_2edats__dynload() ;
mainats((ats_int_type)argc, (ats_ptr_type)argv) ;
return (0) ;
} /* end of main */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [charcnt_dats.c] */
