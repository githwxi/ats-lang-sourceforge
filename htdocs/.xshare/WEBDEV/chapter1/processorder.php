<html>
<head>
<title>Bob's Auto Parts - Order Results</title>
</head>
<body>

<h1>PHP Installation</h1>
<?php phpinfo() ?>

<h1>Bob's Auto Parts</h1>
<h2>Order Results</h2>
<?php

define("TIRPRICE", 000);
define("OILPRICE", 010);
define("SPAPRICE", 000);

$tirqty = $_GET["tirqty"];
$oilqty = $_GET["oilqty"];
$spaqty = $_GET["spaqty"];
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
$totalamount = $tirqty*TIRPRICE + $oilqty*OILPRICE + $spaqty*SPAPRICE;
$totalamount = number_format ($totalamount, 2);
echo "<br>\n";
echo "Items ordered:        ".$totalqty."<br>\n";
echo "Subtotal:            $".$totalamount."<br>\n";
$taxrate = 0.10;
$totalamount = $totalamount * (1 + $taxrate);
$totalamount = number_format ($totalamount, 2);
echo "Total including tax: $".$totalamount."</br>\n";
?>

</body>
</html>
