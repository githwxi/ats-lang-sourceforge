(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

// typedef lint = int_long_t0ype

abst@ype size_t (i:int) = $extype "size_t"
abst@ype ssize_t (i:int) = $extype "ssize_t"

//

sortdef fm = file_mode

//

typedef bytes (n:int) = @[byte][n]
viewdef FILE_v (m:fm, l:addr) = FILE m @ l
viewdef FILE_opt_v (m:fm, l:addr) = option_v (FILE m @ l, l <> null)

//

praxi stdin_is_not_null : [stdin_addr > null] void
praxi stdout_is_not_null : [stdout_addr > null] void
praxi stderr_is_not_null : [stderr_addr > null] void

//

macdef EOF = $extval (int, "EOF")

//

(*

// void clearerr (FILE *stream);

The function [clearerr] clears the end-of-file and error indicators for
the stream pointed to by stream.

*)

fun clearerr {m:fm} (f: &FILE m):<!ref> void
  = "atslib_clearerr"

// ------------------------------------------------

(*

// int fclose (FILE *stream);

The [fclose] function will flush the stream pointed to by fp (writing any
buffered output data using [fflush] and close the underlying file
descriptor. The behaviour of [fclose] is undefined if the stream parameter
is an illegal pointer, or is a descriptor already passed to a previous
invocation of [fclose].

Upon successful completion 0 is returned.  Otherwise, EOF is returned and
the global variable errno is set to indicate the error.  In either case any
further access (including another call to fclose()) to the stream results
in undefined behaviour.

*)

fun fclose_err {m:fm} {l:addr}
  (pf: FILE m @ l | p: ptr l):<!ref> [i:int | i <= 0] int i
  = "atslib_fclose_err"

fun fclose {m:fm} {l:addr} (pf: FILE m @ l | p: ptr l):<!exnref> void
  = "atslib_fclose"

fun fclose_stdin ():<!exnref> void
  = "atslib_fclose_stdin"
fun fclose_stdout ():<!exnref> void
  = "atslib_fclose_stdout"
fun fclose_stderr ():<!exnref> void
  = "atslib_fclose_stderr"

// ------------------------------------------------

(*  

// int feof (FILE *stream);

The function feof() returns a nonzero value if the end of the given file
stream has been reached.

*)

fun feof {m:fm} (f: &FILE m):<!ref> int = "atslib_feof"

// ------------------------------------------------

(*

// int ferror (FILE *stream);

The function [ferror] tests the error indicator for the stream pointed to by
stream, returning non-zero if it is set.  The error indicator can only be
reset by the [clearerr] function.

*)

fun ferror {m:fm} (f: &FILE m):<!ref> int = "atslib_ferror"

// ------------------------------------------------

(*

// int fflush (FILE *stream);

The function fflush forces a write of all user-space buffered data for the
given output or update stream via the streams underlying write function.
The open status of the stream is unaffected.

Upon successful completion 0 is returned.  Otherwise, EOF is returned and
the global variable errno is set to indicate the error.

*)

fun fflush_err {m:fm}
  (pf: file_mode_lte (m, w) | f: &FILE m):<!ref> [i:int | i <= 0] int i
  = "atslib_fflush_err"

fun fflush {m:fm}
  (pf: file_mode_lte (m, w) | f: &FILE m):<!exnref> void
  = "atslib_fflush"

fun fflush_stdout ():<!exnref> void = "atslib_fflush_stdout"

// ------------------------------------------------

(*

// int fgetc (FILE *stream)

[fgetc] reads the next character from stream and returns it as an unsigned
char cast to an int, or EOF on end of file or error.

*)

fun fgetc {m:fm} (pf: file_mode_lte (m, r) | f: &FILE m): int
  = "atslib_fgetc"

// ------------------------------------------------

(*

// int fgetpos(FILE *stream, fpos_t *pos);

The [fgetpos] function stores the file position indicator of the given file
stream in the given position variable. The position variable is of type
fpos_t (which is defined in stdio.h) and is an object that can hold every
possible position in a FILE. [fgetpos] returns zero upon success, and a
non-zero value upon failure.

*)

//

abst@ype fpos_t = $extype "ats_fpos_t_type"

dataview fgetpos_v (addr, int) =
  | {l:addr} fgetpos_v_succ (l, 0) of fpos_t @ l
  | {l:addr} {i:int | i < 0} fgetpos_v_fail (l, i) of fpos_t? @ l

fun fgetpos {m:fm} {l_pos:addr}
  (pf: fpos_t? @ l_pos | f: &FILE m, p: ptr l_pos)
  : [i:int | i <= 0] (fgetpos_v (l_pos, i) | int i)
  = "atslib_fgetpos"

// ------------------------------------------------

(*

// char *fgets (char *str, int size, FILE *stream);

[fgets] reads in at most one less than [size] characters from stream and
stores them into the buffer pointed to by s.  Reading stops after an EOF or
a newline.  If a newline is read, it is stored into the buffer.  A '\0' is
stored after the last character in the buffer.

*)

dataview fgets_v (sz:int, addr, addr) =
  | {n:nat | n < sz} {l_buf:addr | l_buf <> null}
      fgets_v_succ (sz, l_buf, l_buf) of strbuf (sz, n) @ l_buf
  | {l_buf:addr}
      fgets_v_fail (sz, l_buf, null) of bytes (sz) @ l_buf

fun fgets_err {n,sz:int | 0 < n; n <= sz} {m:fm} {l_buf:addr}
  (pf1: file_mode_lte (m, r), pf2: bytes (sz) @ l_buf |
   p: ptr l_buf, n: int n, f: &FILE m)
  : [l:addr] (fgets_v (sz, l_buf, l) | ptr l)
  = "atslib_fgets_err"

fun fgets {n0,sz:int | 0 < n0; n0 <= sz} {m:fm} {l_buf:addr}
  (pf1: file_mode_lte (m, r),
   pf2: !bytes (sz) @ l_buf >>
     [n:nat | n < n0] strbuf (sz, n) @ l_buf |
   p: ptr l_buf, n0: int n0, f: &FILE m)
  :<> void
  = "atslib_fgets"

// ------------------------------------------------

//

(*
 
The function fileno examines the argument stream and returns its integer
descriptor. In case fileno detects that its argument is not a valid stream,
it must return -1 and set errno to EBADF.

*)

(* the type of the function indicates that it should not fail! *)

fun fileno {m:fm} (f: &FILE m): int = "atslib_fileno"

// ------------------------------------------------

(*

// FILE *fopen (const char *path, const char *mode);

The fopen function opens the file whose name is the string pointed to by
path and associates a stream with it.

The argument mode points to a string beginning with one of the follow
ing sequences (Additional characters may follow these sequences.):

  r      Open  text  file  for  reading.  The stream is positioned at the
         beginning of the file.

  r+     Open for reading and writing.  The stream is positioned  at  the
         beginning of the file.

  w      Truncate  file  to  zero length or create text file for writing.
         The stream is positioned at the beginning of the file.

  w+     Open for reading and writing.  The file is created  if  it  does
         not  exist, otherwise it is truncated.  The stream is positioned
         at the beginning of the file.


  a      Open for appending (writing at end of file).  The file is created
         if it does not exist.  The stream is positioned at the end of the
         file.

  a+     Open for reading and appending (writing at end  of  file).   The
         file  is created if it does not exist.  The stream is positioned
         at the end of the file.

*)

fun fopen_err {m:fm}
  (s: string, m: file_mode m): [l:addr] (FILE_opt_v (m, l) | ptr l)
  = "atslib_fopen_err"

fun fopen {m:fm}
  (s: string, m: file_mode m): [l:addr] (FILE m @ l | ptr l)
  = "atslib_fopen"

// ------------------------------------------------

(*

// int fputc (int c, FILE *stream)

The function [fputc] writes the given character ch to the given output
stream.  The return value is the character, unless there is an error, in
which case the return value is EOF.

*)

fun fputc_err {m:fm} (pf: file_mode_lte (m, w) | c: char, f: &FILE m): int
  = "atslib_fputc_err"

fun fputc {m:fm} (pf: file_mode_lte (m, w) | c: char, f: &FILE m): void
  = "atslib_fputc"

// ------------------------------------------------

(*

// int fputs (const char* s, FILE *stream)

The function [fputs] writes a string to a file. it returns a non-negative
number on success, or EOF on error.

*)

fun fputs_err {n:nat} {m:fm} {l_buf:addr}
  (pf1: !bytes (n) @ l_buf, pf2: file_mode_lte (m, w) |
   p: ptr l_buf, f: &FILE m): int
  = "atslib_fputs_err"

fun fputs {n:nat} {m:fm} {l_buf:addr}
  (pf1: !bytes (n) @ l_buf, pf2: file_mode_lte (m, w) |
   p: ptr l_buf, f: &FILE m): void
  = "atslib_fputs"

// ------------------------------------------------

(*

// size_t fread (void *ptr, size_t size, size_t nmemb, FILE *stream);

The function [fread] reads [nmemb] elements of data, each [size] bytes
long, from the stream pointed to by stream, storing them at the location
given by ptr. The return value is the number of items that are actually
read.

[fread] does not distinguish between end-of-file and error, and callers
must use [feof] and [ferror] to determine which occurred.

*)

fun fread
  {sz:pos} {n_buf,n,nsz:nat | nsz <= n_buf} {m:fm} {l_buf:addr}
  (pf1: file_mode_lte (m, r),
   pf2: !bytes (n_buf) @ l_buf,
   pf3: MUL (n, sz, nsz) |
   p: ptr l_buf, sz: int sz, n: int n, f: &FILE m)
  :<!ref> natLte n
  = "atslib_fread"

fun fread_byte
  {n_buf,n:nat | n <= n_buf} {m:fm} {l_buf:addr}
  (pf1: file_mode_lte (m, r),
   pf2: !bytes (n_buf) @ l_buf |
   p: ptr l_buf, n: int n, f: &FILE m)
  :<!ref> natLte n
  = "atslib_fread_byte"

// ------------------------------------------------

(*

// FILE *freopen (const char *path, const char *mode, FILE *stream);

The [freopen] function opens the file whose name is the string pointed to by
path and associates the stream pointed to by stream with it.  The original
stream (if it exists) is closed.  The mode argument is used just as in the
fopen function.  The primary use of the freopen function is to change the
file associated with a standard text stream (stderr, stdin, or stdout).

*)

exception freopen_exception

fun freopen_err {m_old,m_new:fm} {l_file:addr}
  (pf: FILE m_old @ l_file | s: string, m: file_mode m_new, p: ptr l_file)
  : [l:addr | l == null || l == l_file] (FILE_opt_v (m_new, l) | ptr l)
  = "atslib_freopen_err"

fun freopen {m_old,m_new:fm} {l_file:addr}
  (pf: FILE m_old @ l_file | s: string, m: file_mode m_new, p: ptr l_file)
  : (FILE m_new @ l_file | void)
  = "atslib_freopen"

fun freopen_stdin {m:fm} (s: string):<!exnref> void
  = "atslib_freopen_stdin"

fun freopen_stdout {m:fm} (s: string):<!exnref> void
  = "atslib_freopen_stdout"

fun freopen_stderr {m:fm} (s: string):<!exnref> void
  = "atslib_freopen_stderr"

// ------------------------------------------------

(*

// int fseek (FILE *stream, long offset, int whence)

The [fseek] function sets the file position indicator for the stream
pointed to by stream.  The new position, measured in bytes, is obtained by
adding offset bytes to the position specified by whence.  If whence is set
to [SEEK_SET], [SEEK_CUR], or [SEEK_END], the offset is relative to the
start of the file, the current position indicator, or end-of-file,
respectively.  A successful call to the [fseek] function clears the end-
of-file indicator for the stream and undoes any effects of the [ungetc]
function on the same stream. Upon success, [fseek] returns 0. Otherwise,
it returns -1.

*)

fun fseek {m:fm} (f: &FILE m, offset: lint, whence: int): int
  = "atslib_fseek"

// ------------------------------------------------

(*

// void fsetpos(FILE *stream, const fpos_t *pos);

The [fsetpos] function moves the file position indicator for the given
stream to a location specified by the position object. The type fpos_t is
defined in stdio.h.  The return value for fsetpos() is zero upon success,
non-zero on failure.

*)

fun fsetpos {m:fm} (f: &FILE m, pos: &fpos_t): int
  = "atslib_fsetpos"

// ------------------------------------------------

(*

// long ftell (FILE *stream)

[ftell] returns the current offset of the given file stream upon on
success. Otherwise, -1 is returned and the global variable errno is set to
indicate the error.

*)

fun ftell {m:fm} (f: &FILE m): lint = "atslib_ftell"

// ------------------------------------------------

(*

// size_t fwrite (const void *ptr,  size_t size,  size_t nmemb, FILE *stream);

The function [fwrite] writes [nmemb] elements of data, each [size] bytes
long, to the stream pointed to by stream, obtaining them from the location
given by [ptr]. The return value is the number of items that are actually
written.

*)

fun fwrite
  {sz:pos} {n_buf,n,nsz:nat | nsz <= n_buf} {m:fm} {l_buf:addr}
  (pf1: file_mode_lte (m, w),
   pf2: !bytes (n_buf) @ l_buf,
   pf3: MUL (n, sz, nsz) |
   p: ptr l_buf, sz: int sz, n: int n, f: &FILE m)
  :<!ref> natLte n
  = "atslib_fwrite"

fun fwrite_byte
  {n_buf,n:nat | n <= n_buf} {m:fm} {l_buf:addr}
  (pf1: file_mode_lte (m, w), pf2: !bytes (n_buf) @ l_buf |
   p: ptr l_buf, n: int n, f: &FILE m)
  :<!ref> natLte n
  = "atslib_fwrite_byte"

(*

// perror - print a system error message

The routine [perror] produces a message on the standard error output,
describing the last error encountered during a call to a system or library
function.  First (if s is not NULL and *s is not NUL) the argument string
s is printed, followed by a colon and a blank.  Then the message and a
newline.

*)

fun perror (msg: string): void = "atslib_perror"

// ------------------------------------------------

macdef getc = fgetc

fun getchar (): int = "atslib_getchar"

macdef putc = fputc

fun putchar {c:nat} (c: int c): [i:int | i < 0 || i == c] int i
  = "atslib_putchar"

fun put_string (s: string): int = "atslib_put_string"

// ------------------------------------------------

fun remove (s: string): int

fun rename (s_old: string, s_new: string): int

fun rewind {m:fm} (f: &FILE m): void

fun tmpfile (): [l:addr] (FILE_opt_v (rw, l) | ptr l)
  = "atslib_tmpfile"

(*

// int ungetc(int c, FILE *stream);

[ungetc] pushes [c] back to stream, cast to unsigned char, where it is
available for subsequent read operations.  Pushed-back characters will be
returned in reverse order; only one pushback is guaranteed.

*)

fun ungetc {c:nat} {m:fm}
  (c: int c, f: &FILE m): [i:int | i < 0 || i == c] int i
  = "atslib_ungetc"

(* ****** ****** *)

(* end of [stdio.sats] *)

////

(*

// void setlinebuf (FILE *stream);

The function setlinebuf changes the buffering mode of the given stream to line-buffering.

It returns void and does not modify errno.



fun setfullbuf : {m:fm} {l:addr} (&FILE m @ l | ptr l) -> unit

fun setlinebuf : {m:fm} {l:addr} (&FILE m @ l | ptr l) -> unit

fun setnobuf : {m:fm} {l:addr} (&FILE m @ l | ptr l) -> unit

//

(* Do not call these functions directly! Use fprintf or printf instead! *)
(* If the parameters do not form a valid combination, errno is set to EINVAL and -1 is returned. *)

dynval fprintf_nat :
  {l: addr} (&FILE_v l | ptr l, spec_t, length_t, flags_t, width_t, prec_t, Nat) -> Int

dynval fprintf_literal :
  {n:nat, l1: addr, l2: addr}
    (&FILE_v l1, !read_v (cstr_v (n, l2)) | ptr l1, ptr l2) -> Int

////

// ------------------------------------------------

fscanf	read formatted input from a file
gets	read a string from STDIN (DEPRICATED!)
scanf	read formatted input from STDIN
setbuf	set the buffer for a specific stream
setvbuf	set the buffer and size for a specific stream
sprintf	write formatted output to a buffer
sscanf	read formatted input from a buffer
tmpnam generate a unique file name (DEPRICATED!)
vprintf, vfprintf, and vsprintf	write formatted output with variable argument lists
