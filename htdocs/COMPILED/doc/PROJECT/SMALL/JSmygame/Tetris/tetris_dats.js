/*
**
** The JavaScript code is generated by atscc2js
** The starting compilation time is: 2015-6-29: 15h:18m
**
*/

/* ATSextcode_beg() */
//
var
theKeyDowns =
  $(document).asEventStream("keydown")
//
var
theKeyDowns =
theKeyDowns.doAction(".preventDefault")
//
/* ATSextcode_end() */

/* ATSextcode_beg() */
//
var theStage = 0;
var theStageNP = 0;
//
function
theGame_tick(event)
{
//
  theAutoplay_fact();
  thePiece_handle_if();
//
  theStage.update();
  theStageNP.update();
//
  return;
}
//
function
theGame_initize()
{
  theStage = new createjs.Stage("theGameCanvas_main");
  theStageNP = new createjs.Stage("theGameCanvas_np"); // theNextPiece
  createjs.Ticker.setInterval(25); // FPS=1000/25=40
  createjs.Ticker.addEventListener("tick", theGame_tick);
}
//
function
theScore_incby(delta)
{
    var
    score_well =
    document.getElementById("score_well");
    score_well.innerHTML =
    String(parseInt(score_well.innerHTML)+delta);
}
function
theScore_reset(score)
{
    document.getElementById("score_well").innerHTML = score;
}
//
/* ATSextcode_end() */

/* ATSextcode_beg() */
//
function
theStage_addChild(x)
{
  theStage.addChild(x.createjs); return;
}
//
function
theStage_removeChild(x)
{
  theStage.removeChild(x.createjs); return;
}
//
function
theStageNP_addChild(x)
{
  theStageNP.addChild(x.createjs); return;
}
//
function
theStageNP_removeChild(x)
{
  theStageNP.removeChild(x.createjs); return;
}
//
/* ATSextcode_end() */

var tetris__statmp1

var tetris__statmp4

var tetris__statmp5

var tetris__statmp6

var tetris__statmp7

var tetris__statmp18

function
theGameStatus_get()
{
//
// knd = 0
  var tmpret2
  var tmplab, tmplab_js
//
  // __patsflab_theGameStatus_get
  tmpret2 = ats2jspre_ref_get_elt(tetris__statmp1);
  return tmpret2;
} // end-of-function


function
theGameStatus_set(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_theGameStatus_set
  ats2jspre_ref_set_elt(tetris__statmp1, arg0);
  return/*_void*/;
} // end-of-function


function
theGameTQuota_get()
{
//
// knd = 0
  var tmpret8
  var tmplab, tmplab_js
//
  // __patsflab_theGameTQuota_get
  tmpret8 = ats2jspre_ref_get_elt(tetris__statmp5);
  return tmpret8;
} // end-of-function


function
theGameTQuota_reset()
{
//
// knd = 0
  var tmp10
  var tmplab, tmplab_js
//
  // __patsflab_theGameTQuota_reset
  tmp10 = ats2jspre_ref_get_elt(tetris__statmp4);
  ats2jspre_ref_set_elt(tetris__statmp5, tmp10);
  return/*_void*/;
} // end-of-function


function
theGameTQuota_update()
{
//
// knd = 0
  var tmp12
  var tmp13
  var tmp14
  var tmplab, tmplab_js
//
  // __patsflab_theGameTQuota_update
  tmp12 = ats2jspre_ref_get_elt(tetris__statmp5);
  tmp14 = ats2jspre_ref_get_elt(tetris__statmp7);
  tmp13 = ats2jspre_sub_double_double(tmp12, tmp14);
  ats2jspre_ref_set_elt(tetris__statmp5, tmp13);
  return/*_void*/;
} // end-of-function


function
theGameTQuota_delta_space()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_theGameTQuota_delta_space
  ats2jspre_ref_set_elt(tetris__statmp7, 101.0);
  return/*_void*/;
} // end-of-function


function
theGameTQuota_delta_reset()
{
//
// knd = 0
  var tmp17
  var tmplab, tmplab_js
//
  // __patsflab_theGameTQuota_delta_reset
  tmp17 = ats2jspre_ref_get_elt(tetris__statmp6);
  ats2jspre_ref_set_elt(tetris__statmp7, tmp17);
  return/*_void*/;
} // end-of-function


function
tetris__theScore_getinc_delta_7()
{
//
// knd = 0
  var tmpret19
  var tmp20
  var tmp22
  var tmplab, tmplab_js
//
  // __patsflab_tetris__theScore_getinc_delta_7
  tmp20 = ats2jspre_ref_get_elt(tetris__statmp18);
  tmp22 = ats2jspre_add_int0_int0(tmp20, 1);
  ats2jspre_ref_set_elt(tetris__statmp18, tmp22);
  // ATScaseofseq_beg
  tmplab_js = 1;
  while(true) {
    tmplab = tmplab_js; tmplab_js = 0;
    switch(tmplab) {
      // ATSbranchseq_beg
      case 1: // __atstmplab0
      if(!ATSCKpat_int(tmp20, 1)) { tmplab_js = 3; break; }
      case 2: // __atstmplab1
      tmpret19 = 20;
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 3: // __atstmplab2
      if(!ATSCKpat_int(tmp20, 2)) { tmplab_js = 5; break; }
      case 4: // __atstmplab3
      tmpret19 = 40;
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 5: // __atstmplab4
      if(!ATSCKpat_int(tmp20, 3)) { tmplab_js = 7; break; }
      case 6: // __atstmplab5
      tmpret19 = 80;
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 7: // __atstmplab6
      tmpret19 = 10;
      break;
      // ATSbranchseq_end
    } // end-of-switch
    if (tmplab_js === 0) break;
  } // endwhile
  // ATScaseofseq_end
  return tmpret19;
} // end-of-function


function
tetris__theScore_reset_delta_8()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_tetris__theScore_reset_delta_8
  ats2jspre_ref_set_elt(tetris__statmp18, 0);
  return/*_void*/;
} // end-of-function


function
thePiece_handle()
{
//
// knd = 0
  var tmp25
  var tmp26
  var tmp28
  var tmp30
  var tmp31
  var tmplab, tmplab_js
//
  // __patsflab_thePiece_handle
  tmp25 = thePiece_get();
  tmp26 = Piece_ymove_dn(tmp25);
  tmp28 = ats2jspre_neg_bool0(tmp26);
  if(tmp28) {
    Piece_dump_blocks(tmp25);
  } else {
    // ATSINSmove_void
  } // endif
  tmp30 = ats2jspre_neg_bool0(tmp26);
  if(tmp30) {
    theGameTQuota_delta_reset();
  } else {
    // ATSINSmove_void
  } // endif
  tmp31 = ats2jspre_neg_bool0(tmp26);
  if(tmp31) {
    thePiece_theNextPiece_update();
  } else {
    // ATSINSmove_void
  } // endif
  return/*_void*/;
} // end-of-function


function
thePiece_handle_if()
{
//
// knd = 0
  var tmp33
  var tmp34
  var tmp35
  var tmp36
  var tmp39
  var tmp40
  var tmplab, tmplab_js
//
  // __patsflab_thePiece_handle_if
  tmp33 = theGameStatus_get();
  tmp34 = ats2jspre_neq_int0_int0(tmp33, 0);
  if(tmp34) {
    tmp35 = theGameBoard_rowdel_one();
    if(tmp35) {
      tmp36 = tetris__theScore_getinc_delta_7();
      theScore_incby(tmp36);
    } else {
      tetris__theScore_reset_delta_8();
      theGameTQuota_update();
      tmp39 = theGameTQuota_get();
      tmp40 = ats2jspre_gt_double_double(tmp39, 0.0);
      if(tmp40) {
        // ATSINSmove_void
      } else {
        theGameTQuota_reset();
        thePiece_handle();
      } // endif
    } // endif
  } else {
    // ATSINSmove_void
  } // endif
  return/*_void*/;
} // end-of-function


function
theGame_play()
{
//
// knd = 0
  var tmp48
  var tmp50
  var tmp55
  var tmplab, tmplab_js
//
  // __patsflab_theGame_play
  tmp48 = theGameStatus_get();
  tmp50 = ats2jspre_eq_int0_int0(tmp48, 0);
  if(tmp50) {
    theGameBoard_clear();
    theGameStatus_set(1);
    thePiece_theNextPiece_update();
    tetris__theScore_reset_delta_8();
    theScore_reset(0);
  } else {
    // ATSINSmove_void
  } // endif
  tmp55 = ats2jspre_lt_int0_int0(tmp48, 0);
  if(tmp55) {
    theGameStatus_set(1);
  } else {
    // ATSINSmove_void
  } // endif
  return/*_void*/;
} // end-of-function


function
theGame_auto()
{
//
// knd = 0
  var tmp57
  var tmp59
  var tmp62
  var tmp65
  var tmp67
  var tmp68
  var tmplab, tmplab_js
//
  // __patsflab_theGame_auto
  tmp57 = theGameStatus_get();
  tmp59 = ats2jspre_eq_int0_int0(tmp57, 0);
  if(tmp59) {
    theGameBoard_clear();
    tmp62 = ats2jspre_neg_int1(1);
    theGameStatus_set(tmp62);
    thePiece_theNextPiece_update();
    tetris__theScore_reset_delta_8();
    theScore_reset(0);
  } else {
    // ATSINSmove_void
  } // endif
  tmp65 = ats2jspre_gt_int0_int0(tmp57, 0);
  if(tmp65) {
    tmp67 = ats2jspre_neg_int1(1);
    theGameStatus_set(tmp67);
    tmp68 = thePiece_get();
    theGame_autoplay_piece(tmp68);
  } else {
    // ATSINSmove_void
  } // endif
  return/*_void*/;
} // end-of-function


function
theGame_stop()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_theGame_stop
  theGameStatus_set(0);
  thePiece_dump_blocks();
  theGameTQuota_reset();
  return/*_void*/;
} // end-of-function

// dynloadflag_minit
var _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_dats__dynloadflag = 0;

function
_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_dats__dynload()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // ATSdynload()
  // ATSdynloadflag_sta(_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_dats__dynloadflag(149))
  if(ATSCKiseqz(_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_dats__dynloadflag)) {
    _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_dats__dynloadflag = 1 ; // flag is set
    theGame_initize();
    tetris__statmp1 = ats2jspre_ref(0);
    tetris__statmp4 = ats2jspre_ref(100.0);
    tetris__statmp5 = ats2jspre_ref(100.0);
    tetris__statmp6 = ats2jspre_ref(15.0);
    tetris__statmp7 = ats2jspre_ref(15.0);
    tetris__statmp18 = ats2jspre_ref(0);
    tetris_block_initize();
    tetris_piece_initize();
    tetris_keyboard_initize();
    tetris_autoplay_initize();
    tetris_gameboard_initize();
  } // endif
  return/*_void*/;
} // end-of-function


function
tetris_initize()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmygame_057_Tetris_057_tetris_056_dats__dynload();
  return/*_void*/;
} // end-of-function


/* ****** ****** */

/* end-of-compilation-unit */
