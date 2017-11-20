/*
**
** The JavaScript code is generated by atscc2js
** The starting compilation time is: 2017-8-21: 15h:54m
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

var statmp77

var statmp79

var statmp83

var statmp87

function
__patsfun_41__closurerize()
{
  return [function(cenv, arg0, arg1) { return __patsfun_41(arg0, arg1); }];
}


function
__patsfun_56__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_56(arg0); }];
}


function
__patsfun_57__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_57(arg0); }];
}


function
__patsfun_58__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_58(arg0); }];
}


function
__patsfun_31__31__1__closurerize(env0)
{
  return [function(cenv, arg0, arg1) { return __patsfun_31__31__1(cenv[1], arg0, arg1); }, env0];
}


function
__patsfun_63__closurerize()
{
  return [function(cenv) { return __patsfun_63(); }];
}


function
__patsfun_31__31__2__closurerize(env0)
{
  return [function(cenv, arg0, arg1) { return __patsfun_31__31__2(cenv[1], arg0, arg1); }, env0];
}


function
__patsfun_66__closurerize()
{
  return [function(cenv) { return __patsfun_66(); }];
}


function
__patsfun_33__33__1__closurerize(env0)
{
  return [function(cenv, arg0, arg1) { return __patsfun_33__33__1(cenv[1], arg0, arg1); }, env0];
}


function
__patsfun_34__34__1__closurerize(env0, env1)
{
  return [function(cenv, arg0, arg1) { return __patsfun_34__34__1(cenv[1], cenv[2], arg0, arg1); }, env0, env1];
}


function
__patsfun_72__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_72(arg0); }];
}


function
__patsfun_44__44__1__closurerize(env0, env1)
{
  return [function(cenv, arg0, arg1) { return __patsfun_44__44__1(cenv[1], cenv[2], arg0, arg1); }, env0, env1];
}


function
__patsfun_4__4__1__closurerize(env0, env1)
{
  return [function(cenv, arg0) { return __patsfun_4__4__1(cenv[1], cenv[2], arg0); }, env0, env1];
}


function
__patsfun_44__44__2__closurerize(env0, env1)
{
  return [function(cenv, arg0, arg1) { return __patsfun_44__44__2(cenv[1], cenv[2], arg0, arg1); }, env0, env1];
}


function
__patsfun_4__4__2__closurerize(env0, env1)
{
  return [function(cenv, arg0) { return __patsfun_4__4__2(cenv[1], cenv[2], arg0); }, env0, env1];
}


function
__patsfun_44__44__3__closurerize(env0, env1)
{
  return [function(cenv, arg0, arg1) { return __patsfun_44__44__3(cenv[1], cenv[2], arg0, arg1); }, env0, env1];
}


function
__patsfun_4__4__3__closurerize(env0, env1)
{
  return [function(cenv, arg0) { return __patsfun_4__4__3(cenv[1], cenv[2], arg0); }, env0, env1];
}


function
__patsfun_90__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_90(arg0); }];
}


function
__patsfun_91__closurerize(env0, env1)
{
  return [function(cenv, arg0, arg1) { return __patsfun_91(cenv[1], cenv[2], arg0, arg1); }, env0, env1];
}


function
__patsfun_92__closurerize(env0, env1, env2)
{
  return [function(cenv) { return __patsfun_92(cenv[1], cenv[2], cenv[3]); }, env0, env1, env2];
}


function
__patsfun_95__closurerize(env0)
{
  return [function(cenv) { return __patsfun_95(cenv[1]); }, env0];
}


function
__patsfun_97__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_97(arg0); }];
}


function
__patsfun_99__closurerize()
{
  return [function(cenv, arg0) { return __patsfun_99(arg0); }];
}


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_nil()
{
//
// knd = 0
  var tmpret60
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_nil
  tmpret60 = __patsfun_41__closurerize();
  return tmpret60;
} // end-of-function


function
__patsfun_41(arg0, arg1)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_41
  arg1[0](arg1, arg0);
  return/*_void*/;
} // end-of-function


function
__patsfun_56(arg0)
{
//
// knd = 0
  var tmp81
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_56
  tmp81 = 0;
  ats2js_bacon_EStream_bus_push(statmp77, tmp81);
  return/*_void*/;
} // end-of-function


function
__patsfun_57(arg0)
{
//
// knd = 0
  var tmp85
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_57
  tmp85 = 1;
  ats2js_bacon_EStream_bus_push(statmp77, tmp85);
  return/*_void*/;
} // end-of-function


function
__patsfun_58(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_58
  theAction_fwork1_run(arg0);
  return/*_void*/;
} // end-of-function


function
P_session_59()
{
//
// knd = 0
  var tmpret89
  var tmp93
  var tmp98
  var tmp103
  var tmp118
  var tmp125
  var tmp132
  var tmplab, tmplab_js
//
  // __patsflab_P_session_59
  tmp93 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_recv__30__1(__patsfun_63__closurerize());
  tmp98 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_recv__30__2(__patsfun_66__closurerize());
  tmp103 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_send__32__1(__patsfun_72__closurerize());
  tmp132 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_nil();
  tmp125 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_cons__42__3(tmp103, tmp132);
  tmp118 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_cons__42__2(tmp98, tmp125);
  tmpret89 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_cons__42__1(tmp93, tmp118);
  return tmpret89;
} // end-of-function


function
theResult_process_60(arg0)
{
//
// knd = 0
  var tmp92
  var tmplab, tmplab_js
//
  // __patsflab_theResult_process_60
  Start_output("Session over!");
  if(arg0) {
    tmp92 = "true";
  } else {
    tmp92 = "false";
  } // end-of-if
  theResult_set(tmp92);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_recv__30__1(arg0)
{
//
// knd = 0
  var tmpret45__1
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_recv
  tmpret45__1 = __patsfun_31__31__1__closurerize(arg0);
  return tmpret45__1;
} // end-of-function


function
__patsfun_31__31__1(env0, arg0, arg1)
{
//
// knd = 0
  var tmp47__1
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_31
  tmp47__1 = env0[0](env0);
  ats2js_worker_channeg1_recv(arg0, tmp47__1, arg1);
  return/*_void*/;
} // end-of-function


function
__patsfun_63()
{
//
// knd = 0
  var tmpret97
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_63
  tmpret97 = theArg1_get();
  return tmpret97;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_recv__30__2(arg0)
{
//
// knd = 0
  var tmpret45__2
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_recv
  tmpret45__2 = __patsfun_31__31__2__closurerize(arg0);
  return tmpret45__2;
} // end-of-function


function
__patsfun_31__31__2(env0, arg0, arg1)
{
//
// knd = 0
  var tmp47__2
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_31
  tmp47__2 = env0[0](env0);
  ats2js_worker_channeg1_recv(arg0, tmp47__2, arg1);
  return/*_void*/;
} // end-of-function


function
__patsfun_66()
{
//
// knd = 0
  var tmpret102
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_66
  tmpret102 = theArg2_get();
  return tmpret102;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_send__32__1(arg0)
{
//
// knd = 0
  var tmpret48__1
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_send
  tmpret48__1 = __patsfun_33__33__1__closurerize(arg0);
  return tmpret48__1;
} // end-of-function


function
__patsfun_33__33__1(env0, arg0, arg1)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_33
  ats2js_worker_channeg1_send(arg0, __patsfun_34__34__1__closurerize(env0, arg1));
  return/*_void*/;
} // end-of-function


function
__patsfun_34__34__1(env0, env1, arg0, arg1)
{
//
// knd = 0
  var tmp52__1
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_34
  tmp52__1 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__chmsg_parse__70__1(arg1);
  env0[0](env0, tmp52__1);
  env1[0](env1, arg0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__chmsg_parse__70__1(arg0)
{
//
// knd = 0
  var tmpret109__1
  var tmplab, tmplab_js
//
  // __patsflab_chmsg_parse
  tmpret109__1 = arg0;
  return tmpret109__1;
} // end-of-function


function
__patsfun_72(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_72
  theResult_process_60(arg0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_cons__42__1(arg0, arg1)
{
//
// knd = 0
  var tmpret62__1
  var tmp63__1
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_cons
  tmp63__1 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_append__43__1(arg0, arg1);
  tmpret62__1 = tmp63__1;
  return tmpret62__1;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_append__43__1(arg0, arg1)
{
//
// knd = 0
  var tmpret64__1
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_append
  tmpret64__1 = __patsfun_44__44__1__closurerize(arg0, arg1);
  return tmpret64__1;
} // end-of-function


function
__patsfun_44__44__1(env0, env1, arg0, arg1)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_44
  _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__channeg1_append__3__1(arg0, arg1, env0, env1);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__channeg1_append__3__1(arg0, arg1, arg2, arg3)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_append
  arg2[0](arg2, arg0, __patsfun_4__4__1__closurerize(arg1, arg3));
  return/*_void*/;
} // end-of-function


function
__patsfun_4__4__1(env0, env1, arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_4
  env1[0](env1, arg0, env0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_cons__42__2(arg0, arg1)
{
//
// knd = 0
  var tmpret62__2
  var tmp63__2
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_cons
  tmp63__2 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_append__43__2(arg0, arg1);
  tmpret62__2 = tmp63__2;
  return tmpret62__2;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_append__43__2(arg0, arg1)
{
//
// knd = 0
  var tmpret64__2
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_append
  tmpret64__2 = __patsfun_44__44__2__closurerize(arg0, arg1);
  return tmpret64__2;
} // end-of-function


function
__patsfun_44__44__2(env0, env1, arg0, arg1)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_44
  _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__channeg1_append__3__2(arg0, arg1, env0, env1);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__channeg1_append__3__2(arg0, arg1, arg2, arg3)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_append
  arg2[0](arg2, arg0, __patsfun_4__4__2__closurerize(arg1, arg3));
  return/*_void*/;
} // end-of-function


function
__patsfun_4__4__2(env0, env1, arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_4
  env1[0](env1, arg0, env0);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_cons__42__3(arg0, arg1)
{
//
// knd = 0
  var tmpret62__3
  var tmp63__3
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_cons
  tmp63__3 = _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_append__43__3(arg0, arg1);
  tmpret62__3 = tmp63__3;
  return tmpret62__3;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_session_056_sats__channeg1_session_append__43__3(arg0, arg1)
{
//
// knd = 0
  var tmpret64__3
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_append
  tmpret64__3 = __patsfun_44__44__3__closurerize(arg0, arg1);
  return tmpret64__3;
} // end-of-function


function
__patsfun_44__44__3(env0, env1, arg0, arg1)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_44
  _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__channeg1_append__3__3(arg0, arg1, env0, env1);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_contrib_057_libatscc2js_057_ATS2_055_0_056_3_056_2_057_SATS_057_Worker_057_channel_056_sats__channeg1_append__3__3(arg0, arg1, arg2, arg3)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_append
  arg2[0](arg2, arg0, __patsfun_4__4__3__closurerize(arg1, arg3));
  return/*_void*/;
} // end-of-function


function
__patsfun_4__4__3(env0, env1, arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_4
  env1[0](env1, arg0, env0);
  return/*_void*/;
} // end-of-function


function
P_thunkify_88(arg0)
{
//
// knd = 0
  var tmpret133
  var tmp136
  var tmplab, tmplab_js
//
  // __patsflab_P_thunkify_88
  tmp136 = __patsfun_90__closurerize();
  tmpret133 = __patsfun_91__closurerize(arg0, tmp136);
  return tmpret133;
} // end-of-function


function
fwork1_89(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_fwork1_89
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
__patsfun_90(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_90
  fwork1_89(arg0);
  return/*_void*/;
} // end-of-function


function
__patsfun_91(env0, env1, arg0, arg1)
{
//
// knd = 0
  var tmp140
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_91
  tmp140 = __patsfun_92__closurerize(env0, arg0, arg1);
  theAction_fwork01_set(tmp140, env1);
  return/*_void*/;
} // end-of-function


function
__patsfun_92(env0, env1, env2)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_92
  ats2js_worker_channeg1_session_run__53__1(env0, env1, env2);
  return/*_void*/;
} // end-of-function


function
ats2js_worker_channeg1_session_run__53__1(arg0, arg1, arg2)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_run
  arg0[0](arg0, arg1, arg2);
  return/*_void*/;
} // end-of-function


function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_2_057_introxmpl1_client_056_dats__theSession_loop()
{
//
// knd = 0
  var tmp142
  var tmp149
  var tmp154
  var tmplab, tmplab_js
//
  // __patsflab_theSession_loop
  tmp142 = ats2js_worker_channeg0_new_file("./introxmpl1_server_dats_.js");
  tmp149 = __patsfun_95__closurerize(tmp142);
  tmp154 = __patsfun_99__closurerize();
  theAction_fwork01_set(tmp149, tmp154);
  return/*_void*/;
} // end-of-function


function
__patsfun_95(env0)
{
//
// knd = 0
  var tmp145
  var tmp146
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_95
  tmp146 = P_session_59();
  tmp145 = P_thunkify_88(tmp146);
  ats2js_worker_channeg1_session_run__53__2(tmp145, env0, __patsfun_97__closurerize());
  return/*_void*/;
} // end-of-function


function
ats2js_worker_channeg1_session_run__53__2(arg0, arg1, arg2)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_channeg1_session_run
  arg0[0](arg0, arg1, arg2);
  return/*_void*/;
} // end-of-function


function
__patsfun_97(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_97
  ats2js_worker_channeg1_close(arg0);
  _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_2_057_introxmpl1_client_056_dats__theSession_loop();
  return/*_void*/;
} // end-of-function


function
fwork1_98(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab_fwork1_98
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
__patsfun_99(arg0)
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // __patsflab___patsfun_99
  fwork1_98(arg0);
  return/*_void*/;
} // end-of-function

// dynloadflag_minit
var _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_2_057_introxmpl1_client_056_dats__dynloadflag = 0;

function
_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_2_057_introxmpl1_client_056_dats__dynload()
{
//
// knd = 0
  var tmplab, tmplab_js
//
  // ATSdynload()
  // ATSdynloadflag_sta(_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_2_057_introxmpl1_client_056_dats__dynloadflag(215))
  if(ATSCKiseqz(_057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_2_057_introxmpl1_client_056_dats__dynloadflag)) {
    _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_2_057_introxmpl1_client_056_dats__dynloadflag = 1 ; // flag is set
    statmp77 = ats2js_bacon_Bacon_new_bus();
    statmp79 = ats2js_bacon_EStream_onValue_method(Start_clicks);
    statmp79[0](statmp79, __patsfun_56__closurerize());
    statmp83 = ats2js_bacon_EStream_onValue_method(theResult_clicks);
    statmp83[0](statmp83, __patsfun_57__closurerize());
    statmp87 = ats2js_bacon_EStream_onValue_method(statmp77);
    statmp87[0](statmp87, __patsfun_58__closurerize());
    _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_2_057_introxmpl1_client_056_dats__theSession_loop();
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
  _057_home_057_hwxi_057_Research_057_ATS_055_Postiats_057_doc_057_EXAMPLE_057_EFFECTIVATS_057_ssntyped_055_channels_055_2_057_introxmpl1_client_056_dats__dynload();
  return/*_void*/;
} // end-of-function


/* ATSextcode_beg() */
//
jQuery(document).ready(function(){introxmpl1_client_initize();});
//
/* ATSextcode_end() */

/* ****** ****** */

/* end-of-compilation-unit */
