/*
**
** The JavaScript code is generated by atscc2js
** The starting compilation time is: 2017-8-21: 15h:45m
**
*/

/* ATSextcode_beg() */
//
function
ats2js_worker_channeg0_new_file
  (file) { var chn = new Worker(file); return chn; }
//
/* ATSextcode_end() */

/* ATSextcode_beg() */
//
function
ats2js_worker_channeg0_close(chn) { return chn.terminate(); }
function
ats2js_worker_channeg1_close(chn) { return chn.terminate(); }
//
/* ATSextcode_end() */

/* ATSextcode_beg() */
//
function
ats2js_worker_channeg0_send(chn, k0)
{
  chn.onmessage =
  function(event)
    { return ats2jspre_cloref2_app(k0, chn, event.data); };
  return/*void*/;
}
function
ats2js_worker_channeg0_recv(chn, x0, k0)
{
  chn.postMessage(x0); return ats2jspre_cloref1_app(k0, chn);
}
//
function
ats2js_worker_channeg1_send
  (chn, k0)
{
  return ats2js_worker_channeg0_send(chn, k0);
}
function
ats2js_worker_channeg1_recv
  (chn, x0, k0)
{
  return ats2js_worker_channeg0_recv(chn, x0, k0);
}
//
/* ATSextcode_end() */

/* ATSextcode_beg() */
//
var
Start_clicks =
  $("#Start").asEventStream("click")
var
theResult_clicks =
  $("#theResult").asEventStream("click")
//
/* ATSextcode_end() */

/* ATSextcode_beg() */
//
function
theArg1_get()
{
  return parseInt(document.getElementById("theArg1_input").value);
}
function
theArg2_get()
{
  return parseInt(document.getElementById("theArg2_input").value);
}
function
theResult_set(output)
{
  return document.getElementById("theResult_output").value = output;
}
//
function
Start_reset()
{
  document.getElementById("theArg1_input").value = "";
  document.getElementById("theArg2_input").value = "";
  document.getElementById("theResult_output").value = "";
}
function
Start_output(msg)
{
  document.getElementById("Start_output").innerHTML = msg;
}
//
/* ATSextcode_end() */

/* ATSextcode_beg() */
//
var theAction_fwork0 = 0;
var theAction_fwork1 = 0;
//
function
theAction_fwork0_set(f0)
  { theAction_fwork0 = f0; return; }
function
theAction_fwork1_set(f1)
  { theAction_fwork1 = f1; return; }
function
theAction_fwork01_set(f0, f1)
  { theAction_fwork0 = f0; theAction_fwork1 = f1; return; }
//
function
theAction_fwork0_run()
{
  if(theAction_fwork0)
  {
     var f ;
     f = theAction_fwork0;
     theAction_fwork0 = 0; ats2jspre_cloref0_app(f);
  } ; return /* void */ ;
}
function
theAction_fwork1_run(x)
{
  if(theAction_fwork1) ats2jspre_cloref1_app(theAction_fwork1, x); return;
}
//
/* ATSextcode_end() */

var statmp45

var statmp47

var statmp51

var statmp55

function
__patsfun_30__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_30(arg0); }];
}


function
__patsfun_31__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_31(arg0); }];
}


function
__patsfun_32__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_32(arg0); }];
}


function
__patsfun_35__closurerize(env0)
{
  return [function(cenv) { return __patsfun_35(cenv[1]); }, env0];
}


function
__patsfun_36__closurerize(env0)
{
  return [function(cenv, arg0) { return __patsfun_36(cenv[1], arg0); }, env0];
}


function
__patsfun_37__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_37(arg0); }];
}


function
__patsfun_38__closurerize()
{
  return [function(cenv, arg0, arg1) { return __patsfun_38(arg0, arg1); }];
}


function
__patsfun_42__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_42(arg0); }];
}


function
__patsfun_44__closurerize(env0)
{
  return [function(cenv) { return __patsfun_44(cenv[1]); }, env0];
}


function
__patsfun_46__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_46(arg0); }];
}


function
__patsfun_30(arg0)
{
//
// knd = 0
  var tmp49
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_30
  tmp49 = 0;
  ats2js_bacon_EStream_bus_push(statmp45, tmp49);
  return/*_void*/;
} // end-of-function


function
__patsfun_31(arg0)
{
//
// knd = 0
  var tmp53
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_31
  tmp53 = 1;
  ats2js_bacon_EStream_bus_push(statmp45, tmp53);
  return/*_void*/;
} // end-of-function


function
__patsfun_32(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_32
  theAction_fwork1_run(arg0);
  return/*_void*/;
} // end-of-function


function
P_33(arg0)
{
//
// knd = 0
  var tmp70
  var tmp73
  var tmplab, tmplab_js
//
  // __patsflab_P_33
  tmp70 = __patsfun_35__closurerize(arg0);
  tmp73 = __patsfun_42__closurerize();
  theAction_fwork01_set(tmp70, tmp73);
  return/*_void*/;
} // end-of-function


function
theResult_process_34(arg0)
{
//
// knd = 0
  var tmp75
  var tmplab, tmplab_js
//
  // __patsflab_theResult_process_34
  if(arg0) {
    tmp75 = "true";
  } else {
    tmp75 = "false";
  } // end-of-if
  theResult_set(tmp75);
  return/*_void*/;
} // end-of-function


function
__patsfun_35(env0)
{
//
// knd = 0
  var tmp59
  var tmp60
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_35
  tmp59 = theArg1_get();
  tmp60 = theArg2_get();
  ats2js_worker_channeg1_recv(env0, tmp59, __patsfun_36__closurerize(tmp60));
  return/*_void*/;
} // end-of-function


function
__patsfun_36(env0, arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_36
  ats2js_worker_channeg1_recv(arg0, env0, __patsfun_37__closurerize());
  return/*_void*/;
} // end-of-function


function
__patsfun_37(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_37
  ats2js_worker_channeg1_send(arg0, __patsfun_38__closurerize());
  return/*_void*/;
} // end-of-function


function
__patsfun_38(arg0, arg1)
{
//
// knd = 0
  var tmp64
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_38
  tmp64 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__chmsg_parse__39__1(arg1);
  theResult_process_34(tmp64);
  Start_output("Session over!");
  ats2js_worker_channeg1_close(arg0);
  _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_1_057_introxmpl1_client_056_dats__theSession_loop();
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__chmsg_parse__39__1(arg0)
{
//
// knd = 0
  var tmpret65__1
  var tmplab, tmplab_js
//
  // __patsflab_chmsg_parse
  tmpret65__1 = arg0;
  return tmpret65__1;
} // end-of-function


function
fwork1_41(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_fwork1_41
  // ATScaseofseq_beg
  tmplab_js = 1;
  while(true) {
    tmplab = tmplab_js; tmplab_js = 0;
    switch(tmplab) {
      // ATSbranchseq_beg
      case 1: // __atstmplab18
      if(!ATSCKpat_con0(arg0, 1)) {
        { tmplab_js = 3; break; }
      } // ifnthen
      case 2: // __atstmplab19
      theAction_fwork0_run();
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 3: // __atstmplab20
      ats2jspre_alert("The action is ignored!");
      break;
      // ATSbranchseq_end
    } // end-of-switch
    if (tmplab_js === 0) break;
  } // endwhile
  // ATScaseofseq_end
  return/*_void*/;
} // end-of-function


function
__patsfun_42(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_42
  fwork1_41(arg0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_1_057_introxmpl1_client_056_dats__theSession_loop()
{
//
// knd = 0
  var tmp77
  var tmp79
  var tmp84
  var tmplab, tmplab_js
//
  // __patsflab_theSession_loop
  tmp77 = ats2js_worker_channeg0_new_file("./introxmpl1_server_dats_.js");
  tmp79 = __patsfun_44__closurerize(tmp77);
  tmp84 = __patsfun_46__closurerize();
  theAction_fwork01_set(tmp79, tmp84);
  return/*_void*/;
} // end-of-function


function
__patsfun_44(env0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_44
  P_33(env0);
  return/*_void*/;
} // end-of-function


function
fwork1_45(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_fwork1_45
  // ATScaseofseq_beg
  tmplab_js = 1;
  while(true) {
    tmplab = tmplab_js; tmplab_js = 0;
    switch(tmplab) {
      // ATSbranchseq_beg
      case 1: // __atstmplab21
      if(!ATSCKpat_con0(arg0, 0)) {
        { tmplab_js = 3; break; }
      } // ifnthen
      case 2: // __atstmplab22
      Start_reset();
      Start_output("Session is on!");
      theAction_fwork0_run();
      break;
      // ATSbranchseq_end
      // ATSbranchseq_beg
      case 3: // __atstmplab23
      ats2jspre_alert("The action is ignored!");
      break;
      // ATSbranchseq_end
    } // end-of-switch
    if (tmplab_js === 0) break;
  } // endwhile
  // ATScaseofseq_end
  return/*_void*/;
} // end-of-function


function
__patsfun_46(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_46
  fwork1_45(arg0);
  return/*_void*/;
} // end-of-function

// dynloadflag_minit
var _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_1_057_introxmpl1_client_056_dats__dynloadflag = 0;

function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_1_057_introxmpl1_client_056_dats__dynload()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // ATSdynload()
  // ATSdynloadflag_sta(_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_1_057_introxmpl1_client_056_dats__dynloadflag(122))
  if(ATSCKiseqz(_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_1_057_introxmpl1_client_056_dats__dynloadflag)) {
    _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_1_057_introxmpl1_client_056_dats__dynloadflag = 1 ; // flag is set
    statmp45 = ats2js_bacon_Bacon_new_bus();
    statmp47 = ats2js_bacon_EStream_onValue_method(Start_clicks);
    statmp47[0](statmp47, __patsfun_30__closurerize());
    statmp51 = ats2js_bacon_EStream_onValue_method(theResult_clicks);
    statmp51[0](statmp51, __patsfun_31__closurerize());
    statmp55 = ats2js_bacon_EStream_onValue_method(statmp45);
    statmp55[0](statmp55, __patsfun_32__closurerize());
    _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_1_057_introxmpl1_client_056_dats__theSession_loop();
  } // end-of-if
  return/*_void*/;
} // end-of-function


function
introxmpl1_client_initize()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_1_057_introxmpl1_client_056_dats__dynload();
  return/*_void*/;
} // end-of-function


/* ATSextcode_beg() */
//
jQuery(document).ready(function(){introxmpl1_client_initize();});
//
/* ATSextcode_end() */

/* ****** ****** */

/* end-of-compilation-unit */
