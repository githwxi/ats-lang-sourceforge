/*
**
** The JavaScript code is generated by atscc2js
** The starting compilation time is: 2015-6-29: 15h:18m
**
*/

/* ATSextcode_beg() */
function
JSevent_keyCode(x){ return x.keyCode; }
/* ATSextcode_end() */

var tetris_keyboard__statmp0

function
tetris_keyboard__patsfun_0__closurerize()
{
  return [function(cenv, arg0) { return tetris_keyboard__patsfun_0(arg0); }];
}


function
tetris_keyboard__patsfun_8__closurerize()
{
  return [function(cenv, arg0) { return tetris_keyboard__patsfun_8(arg0); }];
}


function
tetris_keyboard__patsfun_0(arg0)
{
//
// knd = 0
  var tmpret1
  var tmplab, tmplab_js
//
  // __patsflab_tetris_keyboard__patsfun_0
  tmpret1 = JSevent_keyCode(arg0);
  return tmpret1;
} // end-of-function


function
theKeyDowns_handle(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_theKeyDowns_handle
  ats2js_bacon_EStream_onValue(tetris_keyboard__statmp0, arg0);
  return/*_void*/;
} // end-of-function


function
tetris_keyboard__aux_up_2()
{
//
// knd = 0
  var tmp4
  var tmp5
  var tmplab, tmplab_js
//
  // __patsflab_tetris_keyboard__aux_up_2
  tmp4 = theGameStatus_get();
  tmp5 = ats2jspre_gt_int0_int0(tmp4, 0);
  if(tmp5) {
    _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_sats__thePiece_lrotate();
  } else {
    // ATSINSmove_void
  } // endif
  return/*_void*/;
} // end-of-function


function
tetris_keyboard__aux_down_3()
{
//
// knd = 0
  var tmp7
  var tmp8
  var tmplab, tmplab_js
//
  // __patsflab_tetris_keyboard__aux_down_3
  tmp7 = theGameStatus_get();
  tmp8 = ats2jspre_gt_int0_int0(tmp7, 0);
  if(tmp8) {
    _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_sats__thePiece_rrotate();
  } else {
    // ATSINSmove_void
  } // endif
  return/*_void*/;
} // end-of-function


function
tetris_keyboard__aux_left_4()
{
//
// knd = 0
  var tmp10
  var tmp11
  var tmplab, tmplab_js
//
  // __patsflab_tetris_keyboard__aux_left_4
  tmp10 = theGameStatus_get();
  tmp11 = ats2jspre_gt_int0_int0(tmp10, 0);
  if(tmp11) {
    _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_sats__thePiece_xmove_l();
  } else {
    // ATSINSmove_void
  } // endif
  return/*_void*/;
} // end-of-function


function
tetris_keyboard__aux_right_5()
{
//
// knd = 0
  var tmp13
  var tmp14
  var tmplab, tmplab_js
//
  // __patsflab_tetris_keyboard__aux_right_5
  tmp13 = theGameStatus_get();
  tmp14 = ats2jspre_gt_int0_int0(tmp13, 0);
  if(tmp14) {
    _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_sats__thePiece_xmove_r();
  } else {
    // ATSINSmove_void
  } // endif
  return/*_void*/;
} // end-of-function


function
tetris_keyboard__aux_space_6()
{
//
// knd = 0
  var tmp16
  var tmp17
  var tmplab, tmplab_js
//
  // __patsflab_tetris_keyboard__aux_space_6
  tmp16 = theGameStatus_get();
  tmp17 = ats2jspre_gt_int0_int0(tmp16, 0);
  if(tmp17) {
    theGameTQuota_delta_space();
  } else {
    // ATSINSmove_void
  } // endif
  return/*_void*/;
} // end-of-function


function
tetris_keyboard__fwork_keycode_7(arg0)
{
//
// knd = 0
  var tmp19
  var tmp20
  var tmp21
  var tmp22
  var tmp23
  var tmplab, tmplab_js
//
  // __patsflab_tetris_keyboard__fwork_keycode_7
  // ATScaseofseq_beg
  tmplab_js = 1;
  while(true) {
    tmplab = tmplab_js; tmplab_js = 0;
    switch(tmplab) {
      // ATSbranchseq_beg
      case 1: // __atstmplab0
      tmp19 = ats2jspre_eq_int0_int0(arg0, 38);
      if(!ATSCKpat_bool(tmp19, true)) { tmplab_js = 2; break; }
      tetris_keyboard__aux_up_2();
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 2: // __atstmplab1
      tmp20 = ats2jspre_eq_int0_int0(arg0, 40);
      if(!ATSCKpat_bool(tmp20, true)) { tmplab_js = 3; break; }
      tetris_keyboard__aux_down_3();
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 3: // __atstmplab2
      tmp21 = ats2jspre_eq_int0_int0(arg0, 37);
      if(!ATSCKpat_bool(tmp21, true)) { tmplab_js = 4; break; }
      tetris_keyboard__aux_left_4();
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 4: // __atstmplab3
      tmp22 = ats2jspre_eq_int0_int0(arg0, 39);
      if(!ATSCKpat_bool(tmp22, true)) { tmplab_js = 5; break; }
      tetris_keyboard__aux_right_5();
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 5: // __atstmplab4
      tmp23 = ats2jspre_eq_int0_int0(arg0, 32);
      if(!ATSCKpat_bool(tmp23, true)) { tmplab_js = 6; break; }
      tetris_keyboard__aux_space_6();
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 6: // __atstmplab5
      // ATSINSmove_void
      break;
      // ATSbranchseq_end
    } // end-of-switch
    if (tmplab_js === 0) break;
  } // endwhile
  // ATScaseofseq_end
  return/*_void*/;
} // end-of-function


function
tetris_keyboard__patsfun_8(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_tetris_keyboard__patsfun_8
  tetris_keyboard__fwork_keycode_7(arg0);
  return/*_void*/;
} // end-of-function

// dynloadflag_minit
var _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_keyboard_056_dats__dynloadflag = 0;

function
_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_keyboard_056_dats__dynload()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // ATSdynload()
  // ATSdynloadflag_sta(_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_keyboard_056_dats__dynloadflag(80))
  if(ATSCKiseqz(_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_keyboard_056_dats__dynloadflag)) {
    _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_keyboard_056_dats__dynloadflag = 1 ; // flag is set
    tetris_keyboard__statmp0 = ats2js_bacon_EStream_map(theKeyDowns, tetris_keyboard__patsfun_0__closurerize());
    theKeyDowns_handle(tetris_keyboard__patsfun_8__closurerize());
  } // endif
  return/*_void*/;
} // end-of-function


function
tetris_keyboard_initize()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_keyboard_056_dats__dynload();
  return/*_void*/;
} // end-of-function


/* ****** ****** */

/* end-of-compilation-unit */
