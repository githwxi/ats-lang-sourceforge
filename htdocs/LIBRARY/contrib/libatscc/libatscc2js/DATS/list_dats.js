/*
**
** The JavaScript code is generated by atscc2js
** The starting compilation time is: 2015-5-10: 17h:15m
**
*/

function
ats2jspre_list_make_intrange_2(arg0, arg1)
{
//
// knd = 0
  var tmpret0
  var tmplab, tmplab_js
//
  // __patsflab_list_make_intrange_2
  tmpret0 = ats2jspre_list_make_intrange_3(arg0, arg1, 1);
  return tmpret0;
} // end-of-function


function
ats2jspre_list_make_intrange_3(arg0, arg1, arg2)
{
//
// knd = 0
  var tmpret1
  var tmp12
  var tmp13
  var tmp14
  var tmp15
  var tmp16
  var tmp17
  var tmp18
  var tmp19
  var tmp20
  var tmp21
  var tmp22
  var tmp23
  var tmp24
  var tmp25
  var tmp26
  var tmp27
  var tmp28
  var tmp29
  var tmp30
  var tmp31
  var tmp32
  var tmplab, tmplab_js
//
  // __patsflab_list_make_intrange_3
  // ATScaseofseq_beg
  tmplab_js = 1;
  while(true) {
    tmplab = tmplab_js; tmplab_js = 0;
    switch(tmplab) {
      // ATSbranchseq_beg
      case 1: // __atstmplab0
      tmp12 = ats2jspre_gt_int0_int0(arg2, 0);
      if(!ATSCKpat_bool(tmp12, true)) { tmplab_js = 2; break; }
      tmp13 = ats2jspre_lt_int0_int0(arg0, arg1);
      if(tmp13) {
        tmp17 = ats2jspre_sub_int0_int0(arg1, arg0);
        tmp16 = ats2jspre_add_int0_int0(tmp17, arg2);
        tmp15 = ats2jspre_sub_int0_int0(tmp16, 1);
        tmp14 = ats2jspre_div_int0_int0(tmp15, arg2);
        tmp20 = ats2jspre_sub_int0_int0(tmp14, 1);
        tmp19 = ats2jspre_mul_int0_int0(tmp20, arg2);
        tmp18 = ats2jspre_add_int0_int0(arg0, tmp19);
        tmp21 = null;
        tmpret1 = _ats2jspre_list_loop1_2(tmp14, tmp18, arg2, tmp21);
      } else {
        tmpret1 = null;
      } // endif
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 2: // __atstmplab1
      tmp22 = ats2jspre_lt_int0_int0(arg2, 0);
      if(!ATSCKpat_bool(tmp22, true)) { tmplab_js = 3; break; }
      tmp23 = ats2jspre_gt_int0_int0(arg0, arg1);
      if(tmp23) {
        tmp24 = ats2jspre_neg_int0(arg2);
        tmp28 = ats2jspre_sub_int0_int0(arg0, arg1);
        tmp27 = ats2jspre_add_int0_int0(tmp28, tmp24);
        tmp26 = ats2jspre_sub_int0_int0(tmp27, 1);
        tmp25 = ats2jspre_div_int0_int0(tmp26, tmp24);
        tmp31 = ats2jspre_sub_int0_int0(tmp25, 1);
        tmp30 = ats2jspre_mul_int0_int0(tmp31, tmp24);
        tmp29 = ats2jspre_sub_int0_int0(arg0, tmp30);
        tmp32 = null;
        tmpret1 = _ats2jspre_list_loop2_3(tmp25, tmp29, tmp24, tmp32);
      } else {
        tmpret1 = null;
      } // endif
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 3: // __atstmplab2
      tmpret1 = null;
      break;
      // ATSbranchseq_end
    } // end-of-switch
    if (tmplab_js === 0) break;
  } // endwhile
  // ATScaseofseq_end
  return tmpret1;
} // end-of-function


function
_ats2jspre_list_loop1_2(arg0, arg1, arg2, arg3)
{
//
// knd = 1
  var apy0
  var apy1
  var apy2
  var apy3
  var tmpret2
  var tmp3
  var tmp4
  var tmp5
  var tmp6
  var funlab_js
  var tmplab, tmplab_js
//
  while(true) {
    funlab_js = 0;
    // __patsflab__ats2jspre_list_loop1_2
    tmp3 = ats2jspre_gt_int0_int0(arg0, 0);
    if(tmp3) {
      tmp4 = ats2jspre_sub_int0_int0(arg0, 1);
      tmp5 = ats2jspre_sub_int0_int0(arg1, arg2);
      tmp6 = [arg1, arg3];
      // ATStailcalseq_beg
      apy0 = tmp4;
      apy1 = tmp5;
      apy2 = arg2;
      apy3 = tmp6;
      arg0 = apy0;
      arg1 = apy1;
      arg2 = apy2;
      arg3 = apy3;
      funlab_js = 1; // __patsflab__ats2jspre_list_loop1_2
      // ATStailcalseq_end
    } else {
      tmpret2 = arg3;
    } // endif
    if (funlab_js > 0) continue; else return tmpret2;
  } // endwhile-fun
} // end-of-function


function
_ats2jspre_list_loop2_3(arg0, arg1, arg2, arg3)
{
//
// knd = 1
  var apy0
  var apy1
  var apy2
  var apy3
  var tmpret7
  var tmp8
  var tmp9
  var tmp10
  var tmp11
  var funlab_js
  var tmplab, tmplab_js
//
  while(true) {
    funlab_js = 0;
    // __patsflab__ats2jspre_list_loop2_3
    tmp8 = ats2jspre_gt_int0_int0(arg0, 0);
    if(tmp8) {
      tmp9 = ats2jspre_sub_int0_int0(arg0, 1);
      tmp10 = ats2jspre_add_int0_int0(arg1, arg2);
      tmp11 = [arg1, arg3];
      // ATStailcalseq_beg
      apy0 = tmp9;
      apy1 = tmp10;
      apy2 = arg2;
      apy3 = tmp11;
      arg0 = apy0;
      arg1 = apy1;
      arg2 = apy2;
      arg3 = apy3;
      funlab_js = 1; // __patsflab__ats2jspre_list_loop2_3
      // ATStailcalseq_end
    } else {
      tmpret7 = arg3;
    } // endif
    if (funlab_js > 0) continue; else return tmpret7;
  } // endwhile-fun
} // end-of-function


function
ats2jspre_list_length(arg0)
{
//
// knd = 0
  var tmpret44
  var tmplab, tmplab_js
//
  // __patsflab_list_length
  tmpret44 = _ats2jspre_list_loop_10(arg0, 0);
  return tmpret44;
} // end-of-function


function
_ats2jspre_list_loop_10(arg0, arg1)
{
//
// knd = 1
  var apy0
  var apy1
  var tmpret45
  var tmp47
  var tmp48
  var funlab_js
  var tmplab, tmplab_js
//
  while(true) {
    funlab_js = 0;
    // __patsflab__ats2jspre_list_loop_10
    // ATScaseofseq_beg
    tmplab_js = 1;
    while(true) {
      tmplab = tmplab_js; tmplab_js = 0;
      switch(tmplab) {
        // ATSbranchseq_beg
        case 1: // __atstmplab7
        if(ATSCKptriscons(arg0)) { tmplab_js = 4; break; }
        case 2: // __atstmplab8
        tmpret45 = arg1;
        break;
        // ATSbranchseq_end
        // ATSbranchseq_beg
        case 3: // __atstmplab9
        case 4: // __atstmplab10
        tmp47 = arg0[1];
        tmp48 = ats2jspre_add_int1_int1(arg1, 1);
        // ATStailcalseq_beg
        apy0 = tmp47;
        apy1 = tmp48;
        arg0 = apy0;
        arg1 = apy1;
        funlab_js = 1; // __patsflab__ats2jspre_list_loop_10
        // ATStailcalseq_end
        break;
        // ATSbranchseq_end
      } // end-of-switch
      if (tmplab_js === 0) break;
    } // endwhile
    // ATScaseofseq_end
    if (funlab_js > 0) continue; else return tmpret45;
  } // endwhile-fun
} // end-of-function


function
ats2jspre_list_get_at(arg0, arg1)
{
//
// knd = 1
  var apy0
  var apy1
  var tmpret49
  var tmp50
  var tmp51
  var tmp52
  var tmp53
  var funlab_js
  var tmplab, tmplab_js
//
  while(true) {
    funlab_js = 0;
    // __patsflab_list_get_at
    tmp50 = ats2jspre_eq_int1_int1(arg1, 0);
    if(tmp50) {
      tmp51 = arg0[0];
      tmpret49 = tmp51;
    } else {
      tmp52 = arg0[1];
      tmp53 = ats2jspre_sub_int1_int1(arg1, 1);
      // ATStailcalseq_beg
      apy0 = tmp52;
      apy1 = tmp53;
      arg0 = apy0;
      arg1 = apy1;
      funlab_js = 1; // __patsflab_list_get_at
      // ATStailcalseq_end
    } // endif
    if (funlab_js > 0) continue; else return tmpret49;
  } // endwhile-fun
} // end-of-function


function
ats2jspre_list_append(arg0, arg1)
{
//
// knd = 0
  var tmpret54
  var tmp55
  var tmp56
  var tmp57
  var tmplab, tmplab_js
//
  // __patsflab_list_append
  // ATScaseofseq_beg
  tmplab_js = 1;
  while(true) {
    tmplab = tmplab_js; tmplab_js = 0;
    switch(tmplab) {
      // ATSbranchseq_beg
      case 1: // __atstmplab11
      if(ATSCKptriscons(arg0)) { tmplab_js = 4; break; }
      case 2: // __atstmplab12
      tmpret54 = arg1;
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 3: // __atstmplab13
      case 4: // __atstmplab14
      tmp55 = arg0[0];
      tmp56 = arg0[1];
      tmp57 = ats2jspre_list_append(tmp56, arg1);
      tmpret54 = [tmp55, tmp57];
      break;
      // ATSbranchseq_end
    } // end-of-switch
    if (tmplab_js === 0) break;
  } // endwhile
  // ATScaseofseq_end
  return tmpret54;
} // end-of-function


function
ats2jspre_list_reverse(arg0)
{
//
// knd = 0
  var tmpret58
  var tmp59
  var tmplab, tmplab_js
//
  // __patsflab_list_reverse
  tmp59 = null;
  tmpret58 = ats2jspre_list_reverse_append(arg0, tmp59);
  return tmpret58;
} // end-of-function


function
ats2jspre_list_reverse_append(arg0, arg1)
{
//
// knd = 0
  var tmpret60
  var tmplab, tmplab_js
//
  // __patsflab_list_reverse_append
  tmpret60 = _ats2jspre_list_loop_15(arg0, arg1);
  return tmpret60;
} // end-of-function


function
_ats2jspre_list_loop_15(arg0, arg1)
{
//
// knd = 1
  var apy0
  var apy1
  var tmpret61
  var tmp62
  var tmp63
  var tmp64
  var funlab_js
  var tmplab, tmplab_js
//
  while(true) {
    funlab_js = 0;
    // __patsflab__ats2jspre_list_loop_15
    // ATScaseofseq_beg
    tmplab_js = 1;
    while(true) {
      tmplab = tmplab_js; tmplab_js = 0;
      switch(tmplab) {
        // ATSbranchseq_beg
        case 1: // __atstmplab15
        if(ATSCKptriscons(arg0)) { tmplab_js = 4; break; }
        case 2: // __atstmplab16
        tmpret61 = arg1;
        break;
        // ATSbranchseq_end
        // ATSbranchseq_beg
        case 3: // __atstmplab17
        case 4: // __atstmplab18
        tmp62 = arg0[0];
        tmp63 = arg0[1];
        tmp64 = [tmp62, arg1];
        // ATStailcalseq_beg
        apy0 = tmp63;
        apy1 = tmp64;
        arg0 = apy0;
        arg1 = apy1;
        funlab_js = 1; // __patsflab__ats2jspre_list_loop_15
        // ATStailcalseq_end
        break;
        // ATSbranchseq_end
      } // end-of-switch
      if (tmplab_js === 0) break;
    } // endwhile
    // ATScaseofseq_end
    if (funlab_js > 0) continue; else return tmpret61;
  } // endwhile-fun
} // end-of-function


function
ats2jspre_list_take(arg0, arg1)
{
//
// knd = 0
  var tmpret65
  var tmp66
  var tmp67
  var tmp68
  var tmp69
  var tmp70
  var tmplab, tmplab_js
//
  // __patsflab_list_take
  tmp66 = ats2jspre_gt_int1_int1(arg1, 0);
  if(tmp66) {
    tmp67 = arg0[0];
    tmp68 = arg0[1];
    tmp70 = ats2jspre_sub_int1_int1(arg1, 1);
    tmp69 = ats2jspre_list_take(tmp68, tmp70);
    tmpret65 = [tmp67, tmp69];
  } else {
    tmpret65 = null;
  } // endif
  return tmpret65;
} // end-of-function


function
ats2jspre_list_drop(arg0, arg1)
{
//
// knd = 1
  var apy0
  var apy1
  var tmpret71
  var tmp72
  var tmp73
  var tmp74
  var funlab_js
  var tmplab, tmplab_js
//
  while(true) {
    funlab_js = 0;
    // __patsflab_list_drop
    tmp72 = ats2jspre_gt_int1_int1(arg1, 0);
    if(tmp72) {
      tmp73 = arg0[1];
      tmp74 = ats2jspre_sub_int1_int1(arg1, 1);
      // ATStailcalseq_beg
      apy0 = tmp73;
      apy1 = tmp74;
      arg0 = apy0;
      arg1 = apy1;
      funlab_js = 1; // __patsflab_list_drop
      // ATStailcalseq_end
    } else {
      tmpret71 = arg0;
    } // endif
    if (funlab_js > 0) continue; else return tmpret71;
  } // endwhile-fun
} // end-of-function


function
ats2jspre_list_split_at(arg0, arg1)
{
//
// knd = 0
  var tmpret75
  var tmp76
  var tmp77
  var tmplab, tmplab_js
//
  // __patsflab_list_split_at
  tmp76 = ats2jspre_list_take(arg0, arg1);
  tmp77 = ats2jspre_list_drop(arg0, arg1);
  tmpret75 = [tmp76, tmp77];
  return tmpret75;
} // end-of-function


function
ats2jspre_list_insert_at(arg0, arg1, arg2)
{
//
// knd = 0
  var tmpret78
  var tmp79
  var tmp80
  var tmp81
  var tmp82
  var tmp83
  var tmplab, tmplab_js
//
  // __patsflab_list_insert_at
  tmp79 = ats2jspre_gt_int1_int1(arg1, 0);
  if(tmp79) {
    tmp80 = arg0[0];
    tmp81 = arg0[1];
    tmp83 = ats2jspre_sub_int1_int1(arg1, 1);
    tmp82 = ats2jspre_list_insert_at(tmp81, tmp83, arg2);
    tmpret78 = [tmp80, tmp82];
  } else {
    tmpret78 = [arg2, arg0];
  } // endif
  return tmpret78;
} // end-of-function


function
ats2jspre_list_remove_at(arg0, arg1)
{
//
// knd = 0
  var tmpret84
  var tmp85
  var tmp86
  var tmp87
  var tmp88
  var tmp89
  var tmp90
  var tmp91
  var tmp92
  var tmplab, tmplab_js
//
  // __patsflab_list_remove_at
  tmp85 = arg0[0];
  tmp86 = arg0[1];
  tmp87 = ats2jspre_gt_int1_int1(arg1, 0);
  if(tmp87) {
    tmp89 = ats2jspre_sub_int1_int1(arg1, 1);
    tmp88 = ats2jspre_list_remove_at(tmp86, tmp89);
    tmp90 = tmp88[0];
    tmp91 = tmp88[1];
    tmp92 = [tmp85, tmp91];
    tmpret84 = [tmp90, tmp92];
  } else {
    tmpret84 = [tmp85, tmp86];
  } // endif
  return tmpret84;
} // end-of-function


function
ats2jspre_list_app(arg0, arg1)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_list_app
  ats2jspre_list_foreach(arg0, arg1);
  return/*_void*/;
} // end-of-function


function
ats2jspre_list_foreach(arg0, arg1)
{
//
// knd = 1
  var apy0
  var apy1
  var tmp95
  var tmp96
  var funlab_js
  var tmplab, tmplab_js
//
  while(true) {
    funlab_js = 0;
    // __patsflab_list_foreach
    // ATScaseofseq_beg
    tmplab_js = 1;
    while(true) {
      tmplab = tmplab_js; tmplab_js = 0;
      switch(tmplab) {
        // ATSbranchseq_beg
        case 1: // __atstmplab19
        if(ATSCKptriscons(arg0)) { tmplab_js = 4; break; }
        case 2: // __atstmplab20
        // ATSINSmove_void
        break;
        // ATSbranchseq_end
        // ATSbranchseq_beg
        case 3: // __atstmplab21
        case 4: // __atstmplab22
        tmp95 = arg0[0];
        tmp96 = arg0[1];
        arg1[0](arg1, tmp95);
        // ATStailcalseq_beg
        apy0 = tmp96;
        apy1 = arg1;
        arg0 = apy0;
        arg1 = apy1;
        funlab_js = 1; // __patsflab_list_foreach
        // ATStailcalseq_end
        break;
        // ATSbranchseq_end
      } // end-of-switch
      if (tmplab_js === 0) break;
    } // endwhile
    // ATScaseofseq_end
    if (funlab_js > 0) continue; else return/*_void*/;
  } // endwhile-fun
} // end-of-function


function
ats2jspre_list_map(arg0, arg1)
{
//
// knd = 0
  var tmpret98
  var tmp99
  var tmp100
  var tmp101
  var tmp102
  var tmplab, tmplab_js
//
  // __patsflab_list_map
  // ATScaseofseq_beg
  tmplab_js = 1;
  while(true) {
    tmplab = tmplab_js; tmplab_js = 0;
    switch(tmplab) {
      // ATSbranchseq_beg
      case 1: // __atstmplab23
      if(ATSCKptriscons(arg0)) { tmplab_js = 4; break; }
      case 2: // __atstmplab24
      tmpret98 = null;
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 3: // __atstmplab25
      case 4: // __atstmplab26
      tmp99 = arg0[0];
      tmp100 = arg0[1];
      tmp101 = arg1[0](arg1, tmp99);
      tmp102 = ats2jspre_list_map(tmp100, arg1);
      tmpret98 = [tmp101, tmp102];
      break;
      // ATSbranchseq_end
    } // end-of-switch
    if (tmplab_js === 0) break;
  } // endwhile
  // ATScaseofseq_end
  return tmpret98;
} // end-of-function


/* ****** ****** */

/* end-of-compilation-unit */
