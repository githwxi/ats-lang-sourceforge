<?php

/* ****** ****** */

/*
// For building TUTORIATS
*/

/* ****** ****** */

/*
// Author: Hongwei Xi
// Start time: September, 2014
*/

/* ****** ****** */
//
function
tutoriats_fname_dats_c($fname) { return $fname . "_dats.c"; }
function
tutoriats_fname_dats_js($fname) { return $fname . "_dats.js"; }
function
tutoriats_fname_dats_php($fname) { return $fname . "_dats.php"; }
//
/* ****** ****** */

function
tutoriats_exec_retval
  ($command)
{
  $retval = 0;
  $output = array();
  exec($command, $output, $retval);
  return $retval;
}

/* ****** ****** */

/* end of [basics_cats.php] */

?>
