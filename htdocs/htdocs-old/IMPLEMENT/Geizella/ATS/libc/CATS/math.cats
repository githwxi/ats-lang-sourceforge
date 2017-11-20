/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi.
 *
 * ATS is  free software;  you can redistribute it and/or modify it under
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 */

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef _LIBC_MATH_CATS
#define _LIBC_MATH_CATS

/* ****** ****** */

#include <math.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

static inline
ats_double_type
atslib_ceil(ats_double_type x) { return ceil(x); }

static inline
ats_float_type
atslib_ceilf(ats_float_type x) { return ceilf(x); }

static inline
ats_ldouble_type
atslib_ceill(ats_ldouble_type x) {
  return ceill(x);
}

static inline
ats_double_type
atslib_floor(ats_double_type x) { return floor(x); }

static inline
ats_float_type
atslib_floorf(ats_float_type x) { return floorf(x); }

static inline
ats_ldouble_type
atslib_floorl(ats_ldouble_type x) { return floorl(x); }

//

static inline
ats_double_type
atslib_fmod (ats_double_type f1, ats_double_type f2) {
  return fmod(f1, f2) ;
}

static inline
ats_float_type
atslib_fmodf (ats_float_type f1, ats_float_type f2) {
  return fmodf(f1, f2) ;
}

static inline
ats_ldouble_type
atslib_fmodl (ats_ldouble_type f1, ats_ldouble_type f2) {
  return fmodl(f1, f2) ;
}

/* ****** ****** */

static inline
ats_double_type
atslib_sqrt (ats_double_type f) {
  return sqrt(f) ;
}

static inline
ats_float_type
atslib_sqrtf (ats_float_type f) {
  return sqrtf(f) ;
}

static inline
ats_ldouble_type
atslib_sqrtl (ats_ldouble_type f) {
  return sqrtl(f) ;
}

//

static inline
ats_double_type
atslib_cbrt (ats_double_type f) {
  return cbrt(f) ;
}

static inline
ats_float_type
atslib_cbrtf (ats_float_type f) {
  return cbrtf(f) ;
}

static inline
ats_ldouble_type
atslib_cbrtl (ats_ldouble_type f) {
  return cbrtl(f) ;
}

//

static inline
ats_double_type
atslib_pow (ats_double_type f1, ats_double_type f2) {
  return pow(f1, f2) ;
}

static inline
ats_float_type
atslib_powf (ats_float_type f1, ats_float_type f2) {
  return powf(f1, f2) ;
}

static inline
ats_ldouble_type
atslib_powl (ats_ldouble_type f1, ats_ldouble_type f2) {
  return powl(f1, f2) ;
}

/* ****** ****** */

static inline
ats_double_type
atslib_exp(ats_double_type x) { return exp(x); }

static inline
ats_float_type
atslib_expf(ats_float_type x) { return expf(x); }

static inline
ats_ldouble_type
atslib_expl(ats_ldouble_type x) { return expl(x); }

/* ****** ****** */

static inline
ats_double_type
atslib_log(ats_double_type x) { return log(x); }

static inline
ats_float_type
atslib_logf(ats_float_type x) { return logf(x); }

static inline
ats_ldouble_type
atslib_logl(ats_ldouble_type x) { return logl(x); }

/* ****** ****** */

static inline
ats_double_type
atslib_asin(ats_double_type x) { return asin(x); }

static inline
ats_float_type
atslib_asinf(ats_float_type x) { return asinf(x); }

static inline
ats_ldouble_type
atslib_asinl(ats_ldouble_type x) {
  return asinl(x);
}

static inline
ats_double_type
atslib_acos(ats_double_type x) { return acos(x); }

static inline
ats_float_type
atslib_acosf(ats_float_type x) { return acosf(x); }

static inline
ats_ldouble_type
atslib_acosl(ats_ldouble_type x) {
  return acosl(x);
}

static inline
ats_double_type
atslib_atan(ats_double_type x) { return atan(x); }

static inline
ats_float_type
atslib_atanf(ats_float_type x) { return atanf(x); }

static inline
ats_ldouble_type
atslib_atanl(ats_ldouble_type x) { return atanl(x); }

static inline
ats_double_type
atslib_atan2(ats_double_type x, ats_double_type y) {
  return atan2(x, y);
}

static inline
ats_float_type
atslib_atan2f(ats_float_type x, ats_float_type y) {
  return atan2(x, y);
}

static inline
ats_ldouble_type
atslib_atan2l(ats_ldouble_type x, ats_ldouble_type y) {
  return atan2l(x, y);
}

//

static inline
ats_double_type
atslib_asinh(ats_double_type x) { return asinh(x); }

static inline
ats_float_type
atslib_asinhf(ats_float_type x) { return asinhf(x); }

static inline
ats_ldouble_type
atslib_asinhl(ats_ldouble_type x) {
  return asinhl(x);
}

static inline
ats_double_type
atslib_acosh(ats_double_type x) { return acosh(x); }

static inline
ats_float_type
atslib_acoshf(ats_float_type x) { return acoshf(x); }

static inline
ats_ldouble_type
atslib_acoshl(ats_ldouble_type x) {
  return acoshl(x);
}

//

static inline
ats_double_type
atslib_sin(ats_double_type x) { return sin(x); }

static inline
ats_float_type
atslib_sinf(ats_float_type x) { return sinf(x); }

static inline
ats_ldouble_type
atslib_sinl(ats_ldouble_type x) { return sinl(x); }

static inline
ats_double_type
atslib_cos(ats_double_type x) { return cos(x); }

static inline
ats_float_type
atslib_cosf(ats_float_type x) { return cosf(x); }

static inline
ats_ldouble_type
atslib_cosl(ats_ldouble_type x) { return cosl(x); }

static inline
ats_double_type
atslib_tan(ats_double_type x) { return tan(x); }

static inline
ats_float_type
atslib_tanf(ats_float_type x) { return tanf(x); }

static inline
ats_ldouble_type
atslib_tanl(ats_ldouble_type x) { return tanl(x); }

/* ****** ****** */

#endif /* _LIBC_MATH_CATS */

/* end of [math.cats] */
