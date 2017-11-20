// Time: August 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

// The hashtable implementation is based on linear-probing

(* ****** ****** *)

abstype dna_t // boxed type
abst@ype symbol_t = $extype "symbol_t"
abstype symtbl_t // boxed type

fun print_symbol (dna: dna_t, sym: symbol_t): void

fun symtbl_make (dna: dna_t, size: Nat) : symtbl_t
fun symtbl_clear (tbl: symtbl_t) : void = "symtbl_clear"
fun symtbl_search (tbl: symtbl_t, name: string) : int
  = "symtbl_search"
fun symtbl_insert (tbl: symtbl_t, sym: symbol_t, cnt: int) : void
  = "symtbl_insert"

fun symtbl_fold {a:viewt@ype}
  (tbl: symtbl_t, f: !(symbol_t, int, &a) -<cloptr1> void, res: &a) : void

fun symtbl_dna (tbl: symtbl_t): dna_t

(* ****** ****** *)

(* end of [symtbl.sats] *)
