<html>
<head>
<title>Bob's Auto Parts - Order Results</title>
</head>
<body>

<!--
<h1>PHP Info</h1>
<?php phpinfo() ?>
-->

<h1>DOC Info</h1>
<?php

$DOCUMENT_ROOT = $_SERVER['DOCUMENT_ROOT'];
echo ("\$DOCUMENT_ROOT = $DOCUMENT_ROOT<br>") ;
$SERVER_NAME = $_SERVER['SERVER_NAME'];
echo ("\$SERVER_NAME = $SERVER_NAME<br>") ;
$SCRIPT_FILENAME = $_SERVER['SCRIPT_FILENAME'];
echo ("\$SCRIPT_FILENAME = $SCRIPT_FILENAME<br>") ;
$MYDIR= ereg_replace ("/[^/]*$", "", $SCRIPT_FILENAME);
echo ("\$MYDIR = $MYDIR<br>") ;
?>

<h1>Bob's Auto Parts</h1>
<h2>Order Results</h2>
<?php

define("TIRPRICE", "100");
define("OILPRICE", "004");
define("SPAPRICE", "001");

$tirqty = $_REQUEST["tirqty"];
$oilqty = $_REQUEST["oilqty"];
$spaqty = $_REQUEST["spaqty"];
$shipaddr = $_REQUEST["shipaddr"];
//
echo "<p>Order processed at "; echo date ("H:i, jS F");
echo "<br>";
echo "<p>Your order is as follows:";
echo "<br>";
echo "$tirqty tires";
echo "<br>";
echo "$oilqty bottles of oil";
echo "<br>";
echo "$spaqty spark plugs";
echo "<br>";
//
$totalqty = $tirqty + $oilqty + $spaqty;
if ($totalqty == 0) {
  echo "You did not order anything on the previous page!<br>";
  exit;
}
$totalamount = $tirqty*TIRPRICE + $oilqty*OILPRICE + $spaqty*SPAPRICE;
$totalamount = number_format ($totalamount, 2);
echo "<br>\n";
echo "Items ordered:        ".$totalqty."<br>\n";
echo "Subtotal:            $".$totalamount."<br>\n";
$taxrate = 0.10;
$totalamount = $totalamount * (1 + $taxrate);
$totalamount = number_format ($totalamount, 2);
echo "Total including tax: $".$totalamount."</br>\n";
echo "<p>The shipping address for this order:</br>\n";
echo "$shipaddr<br>\n";
?>

<?php
$fname = "orders.txt";
// $fname = "$MYDIR/../orders/orders.txt";
$isexi = file_exists ($fname);
if ($isexi) {
  echo ("The file [$fname] is available!<br>");
} else {
  echo ("The file [$fname] is not available!<br>");
} ;

$fp = fopen($fname, "r");
if(!$fp) {
  echo ("Can't open the file [$fname] for read!<br>");
}
$fp = fopen($fname, "w");
if(!$fp) {
  echo ("Can't open the file [$fname] for write!<br>");
}
fwrite($fp, "Hello!");
fclose($fp);
?>

</body>
</html>
