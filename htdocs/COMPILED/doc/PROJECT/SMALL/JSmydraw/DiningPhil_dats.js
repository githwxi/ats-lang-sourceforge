/*
**
** The JavaScript code is generated by atscc2js
** The starting compilation time is: 2015-8-5: 13h:53m
**
*/

function
__patsfun_4__closurerize(env0)
{
  return [function(cenv) { return __patsfun_4(cenv[1]); }, env0];
}


function
__patsfun_8__closurerize(env0)
{
  return [function(cenv) { return __patsfun_8(cenv[1]); }, env0];
}


function
__patsfun_9__closurerize(env0)
{
  return [function(cenv) { return __patsfun_9(cenv[1]); }, env0];
}


function
__patsfun_11__closurerize(env0)
{
  return [function(cenv) { return __patsfun_11(cenv[1]); }, env0];
}


function
__patsfun_12__closurerize(env0)
{
  return [function(cenv) { return __patsfun_12(cenv[1]); }, env0];
}


function
cloref_app(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_cloref_app
  arg0[0](arg0);
  return/*_void*/;
} // end-of-function


function
rand_int2_1(arg0, arg1)
{
//
// knd = 0
  var tmpret1
  var tmp2
  var tmp3
  var tmplab, tmplab_js
//
  // __patsflab_rand_int2_1
  tmp3 = ats2jspre_JSmath_random();
  tmp2 = ats2jspre_mul_int_double(arg1, tmp3);
  tmpret1 = ats2jspre_add_int_double(arg0, tmp2);
  return tmpret1;
} // end-of-function


function
phil_loop(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_phil_loop
  phil_draw(arg0);
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_think_beg(arg0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_think_beg(arg0)
{
//
// knd = 0
  var tmp7
  var tmplab, tmplab_js
//
  // __patsflab_phil_think_beg
  tmp7 = rand_int2_1(500, 2500);
  setTimeout_cloref(__patsfun_4__closurerize(arg0), tmp7);
  return/*_void*/;
} // end-of-function


function
__patsfun_4(env0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_4
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_think_end(env0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_think_end(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_phil_think_end
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_start(arg0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_start(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_phil_dine_start
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_lfork(arg0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_lfork(arg0)
{
//
// knd = 0
  var tmp12
  var tmp13
  var tmp15
  var tmp16
  var tmplab, tmplab_js
//
  // __patsflab_phil_dine_lfork
  tmp12 = rand_int2_1(250, 1000);
  tmp13 = phil_pick_lfork(arg0);
  tmp15 = ats2jspre_gt_int0_int0(tmp13, 0);
  if(tmp15) {
    phil_draw(arg0);
  } else {
    // ATSINSmove_void
  } // endif
  tmp16 = ats2jspre_eq_int0_int0(tmp13, 0);
  if(tmp16) {
    setTimeout_cloref(__patsfun_8__closurerize(arg0), tmp12);
  } else {
    setTimeout_cloref(__patsfun_9__closurerize(arg0), tmp12);
  } // endif
  return/*_void*/;
} // end-of-function


function
__patsfun_8(env0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_8
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_lfork(env0);
  return/*_void*/;
} // end-of-function


function
__patsfun_9(env0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_9
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_rfork(env0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_rfork(arg0)
{
//
// knd = 0
  var tmp20
  var tmp21
  var tmp23
  var tmp24
  var tmplab, tmplab_js
//
  // __patsflab_phil_dine_rfork
  tmp20 = rand_int2_1(250, 1000);
  tmp21 = phil_pick_rfork(arg0);
  tmp23 = ats2jspre_gt_int0_int0(tmp21, 0);
  if(tmp23) {
    phil_draw(arg0);
  } else {
    // ATSINSmove_void
  } // endif
  tmp24 = ats2jspre_eq_int0_int0(tmp21, 0);
  if(tmp24) {
    setTimeout_cloref(__patsfun_11__closurerize(arg0), tmp20);
  } else {
    setTimeout_cloref(__patsfun_12__closurerize(arg0), tmp20);
  } // endif
  return/*_void*/;
} // end-of-function


function
__patsfun_11(env0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_11
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_rfork(env0);
  return/*_void*/;
} // end-of-function


function
__patsfun_12(env0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_12
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_finish(env0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__phil_dine_finish(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_phil_dine_finish
  phil_return_lfork(arg0);
  phil_return_rfork(arg0);
  phil_loop(arg0);
  return/*_void*/;
} // end-of-function

// dynloadflag_minit
var _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__dynloadflag = 0;

function
_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__dynload()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // ATSdynload()
  // ATSdynloadflag_sta(_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__dynloadflag(88))
  if(ATSCKiseqz(_057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__dynloadflag)) {
    _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__dynloadflag = 1 ; // flag is set
  } // endif
  return/*_void*/;
} // end-of-function


function
my_dynload()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  _057_home_057_hwxi_057_research_057_Postiats_055_contrib_057_git_057_projects_057_SMALL_057_JSmydraw_057_DiningPhil_057_DiningPhil_056_dats__dynload();
  return/*_void*/;
} // end-of-function


/* ATSextcode_beg() */
//
var
mycanvas =
document.getElementById
  ("Patsoptaas-Evaluate-canvas");
//
var
myctx2d0 = mycanvas.getContext( '2d' );
//
var theFks = [1, 1, 1, 1, 1]
//
var Ph0 = { lfork: 0, rfork: 0 }
var Ph1 = { lfork: 0, rfork: 0 }
var Ph2 = { lfork: 0, rfork: 0 }
var Ph3 = { lfork: 0, rfork: 0 }
var Ph4 = { lfork: 0, rfork: 0 }
var thePhs = [Ph0, Ph1, Ph2, Ph3, Ph4]
//
function
phil_pick_lfork
  (id0)
{
//
var
lf0 =
theFks[id0];
if(lf0 > 0)
{
  theFks[id0] = 0;
  thePhs[id0].lfork = 1;
}
return (lf0);
//
} // phil_pick_lfork
//
function
phil_pick_rfork
  (id0)
{
//
var id1 = (id0+1)%5;
var rf1 = theFks[id1];
if(rf1 > 0)
{
  theFks[id1] = 0;
  thePhs[id0].rfork = 1;
}
return (rf1);
//
} // phil_pick_rfork
//
function
phil_return_lfork
  (id0)
{
  var ph = thePhs[id0];
  ph.lfork = 0; theFks[id0] = 1; return;
}
function
phil_return_rfork
  (id0)
{
  var ph = thePhs[id0];
  var id1 = (id0+1)%5
  ph.rfork = 0; theFks[id1] = 1; return;
}
//
function
theCx_get() { return mycanvas.width/2; }
function
theCy_get() { return mycanvas.height/2; }
function
theRadius1_get() { return Math.min(mycanvas.width, mycanvas.height)/2; }
function
theRadius2_get() { return theRadius1_get() / 5; }
//
function
phil_Cx(id)
{
  var r1 = theRadius1_get();
  var r2 = theRadius2_get();
  var theta = Math.PI/2 + id*(2*Math.PI/5);
  return theCx_get() + (r1-r2) * Math.cos(theta);
}
function
phil_Cy(id)
{
  var r1 = theRadius1_get();
  var r2 = theRadius2_get();
  var theta = Math.PI/2 + id*(2*Math.PI/5);
  return theCy_get() - (r1-r2) * Math.sin(theta);
}
//
function
phil_draw(id)
{
  var ph = thePhs[id];
  var Cx = phil_Cx(id);
  var r2 = theRadius2_get();
  var Cy = phil_Cy(id) + 2*r2/5;
  var fg_color = "#000000"; // black
  var bg_color = "#ffffff"; // white
//
  var PI = Math.PI
  var rot = PI/2-id*(2*PI/5)
//
  myctx2d0.beginPath();
  myctx2d0.arc(Cx, Cy, r2, 0, 2*PI, true);
  myctx2d0.closePath();
  myctx2d0.fillStyle = bg_color; myctx2d0.fill();
//
  if (ph.lfork > 0)
  {
    myctx2d0.beginPath();
    myctx2d0.arc(Cx, Cy, r2, rot, rot+PI, true);
    myctx2d0.closePath();
    myctx2d0.fillStyle = fg_color; myctx2d0.fill();
  }
  if (ph.rfork > 0)
  {
    myctx2d0.beginPath();
    myctx2d0.arc(Cx, Cy, r2, rot+PI, rot+2*PI, true);
    myctx2d0.closePath();
    myctx2d0.fillStyle = fg_color; myctx2d0.fill();
  }
//
  return;
}
//
function
DininingPhil_initize()
{
  phil_loop(0);
  phil_loop(1);
  phil_loop(2);
  phil_loop(3);
  phil_loop(4); return;
}
/*
function
DininingPhil_initize() { alert("DininingPhil_initize"); }
*/
//
function
setTimeout_cloref(fwork, ntime)
{
  setTimeout(function(){cloref_app(fwork);return;}, ntime); return;
}
//
jQuery(document).ready(function(){DininingPhil_initize();});
//
/* ATSextcode_end() */

/* ****** ****** */

/* end-of-compilation-unit */