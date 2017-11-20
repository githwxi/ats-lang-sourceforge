//
//
// sum-file.dats -- read lines, parse and tally integers
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// This implementation is as efficient as the C code attached
// at the end of this file.
//
// Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//
//

%{^

#include "libc/CATS/stdio.cats"
#include "libc/CATS/stdlib.cats"

%}

staload "libc/SATS/stdio.sats"
staload "libc/SATS/stdlib.sats"

#define BUFSZ 128

typedef bytes (n:int) = @[byte][n]

fun loop {l_buf:addr}
 (pf_buf: !bytes(BUFSZ) @ l_buf | file: &FILE r, buf: ptr l_buf, sum: int): int =
  let
    val (pf_res | res) = fgets_err (file_mode_lte_r_r, pf_buf | buf, BUFSZ, file)
  in
    if res <> null then begin
      let
        prval fgets_v_succ pf = pf_res
        val i = atoi (!buf)
        prval () = pf_buf := bytes_v_of_strbuf_v pf
      in
        loop (pf_buf | file, buf, sum + i)
      end
    end else begin
      let prval fgets_v_fail pf = pf_res in (pf_buf := pf; sum) end
    end
  end

//

implement main (argc, argv) =
  let
     val (pf_stdin | stdin) = stdin_get ()
     val (pf_ngc, pf_buf | buf) = malloc_ngc (BUFSZ)
     val sum = loop (pf_buf | !stdin, buf, 0)
     val () = free_ngc (pf_ngc, pf_buf | buf)
     val () = stdin_view_set (pf_stdin | (*none*))
  in
     printf ("%i\n", @(sum))
  end

////

/* -*- mode: c -*-
 * $Id: sumcol-gcc.code,v 1.42 2007-05-19 00:42:43 igouy-guest Exp $
 * http://www.bagley.org/~doug/shootout/
 */

#include <stdio.h>
#include <stdlib.h>

#define MAXLINELEN 128

int
main() {
    int sum = 0;
    char line[MAXLINELEN];

    while (fgets(line, MAXLINELEN, stdin)) {
	sum += atoi(line);
    }
    printf("%d\n", sum);
    return(0);
}
