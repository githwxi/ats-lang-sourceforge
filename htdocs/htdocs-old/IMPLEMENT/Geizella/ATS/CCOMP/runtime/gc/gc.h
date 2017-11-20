/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/*                              Hongwei Xi                             */
/*                                                                     */
/***********************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
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
 */

/* ****** ****** */

/* Author: Rick Lavoie (coldfury AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef _ATS_GC_H_
#define _ATS_GC_H_

typedef void** gc_value;

#define GET_NTH_FIELD_PTR(ptr, i) (((gc_value *)ptr) + (i))
#define GET_NTH_FIELD(ptr, i) (*GET_NTH_FIELD_PTR(ptr, i))
#define SET_NTH_FIELD(ptr, i, x) \
  do { (*GET_NTH_FIELD_PTR(ptr, i) = (gc_value)(x)); } while (0)

/* ****** ****** */

#ifdef ATS_MULTITHREAD
#include <pthread.h>
#endif

#include <stdio.h>

#include <stddef.h>

#ifdef _MSC_VER
#define SIGBUS SIGSEGV
#elif (defined (__SVR4) && defined (__sun))
#include <inttypes.h>
#else
#include <stdint.h>
#endif /* _MSC_VER */

#include <string.h> /* for memset */

/* ****** ****** */

#if (__WORDSIZE == 32)
#define BYTES_PER_WORD_LOG 2
#elif (__WORDSIZE == 64)
#define BYTES_PER_WORD_LOG 3
#define TOP_LEVEL_HASH_SIZE_LOG 12
#define TOP_LEVEL_HASH_SIZE (1 << TOP_LEVEL_HASH_SIZE_LOG)
#else
#error "__WORDSIZE is either not set or unknown! Please set an appropriate __WORDSIZE to this architecture!"
#endif

#define BYTES_PER_WORD (1 << BYTES_PER_WORD_LOG)
#define BITS_PER_WORD (BYTES_PER_WORD*8)

#define CHUNK_WORD_SIZE_LOG 11
#define LARGEST_BLOCK_SIZE_IN_CHUNK_LOG CHUNK_WORD_SIZE_LOG
#define LARGEST_BLOCK_SIZE_IN_CHUNK (1 << LARGEST_BLOCK_SIZE_IN_CHUNK_LOG)

#ifdef ATS_MULTITHREAD
extern __thread gc_value free_lists[];
extern __thread gc_value atomic_free_lists[];
#else
extern gc_value free_lists[];
extern gc_value atomic_free_lists[];
#endif

#ifdef ATS_MULTITHREAD
extern int gc_create_pthread(void*(*)(void*), void*, pthread_t*, int);
#endif
extern gc_value gc_big_alloc_word(const size_t, const unsigned int);

// extern gc_value gc_alloc_atomic_word(const unsigned int);
// extern gc_value gc_alloc_word(const unsigned int);
// extern void gc_free(gc_value);
extern gc_value gc_realloc_word(gc_value, const size_t);

extern void gc_init();
extern void gc_markroot(gc_value*, size_t);

extern gc_value gc_allocate_persistant_byte(const size_t);
extern gc_value gc_allocate_persistant_word(const size_t);

extern void gc_free_persistant(gc_value);
extern gc_value gc_reallocate_persistant_byte(gc_value ptr, const size_t);

extern gc_value gc_refresh_atomic_freelist(const unsigned int);
extern gc_value gc_refresh_freelist(const unsigned int);

static inline
__attribute__ ((unused))
unsigned int ones(unsigned int x)
{
  x -= ((x >> 1) & 0x55555555);
  x = (((x >> 2) & 0x33333333) + (x & 0x33333333));
  x = (((x >> 4) + x) & 0x0f0f0f0f);
  x += (x >> 8);
  x += (x >> 16);
  return (x & 0x0000003f);
}

static inline
__attribute__ ((unused))
unsigned int ceil_log2(unsigned int x)
{
  int y = (x & (x - 1));

  y |= -y;
  y >>= (32 - 1);
  x |= (x >> 1);
  x |= (x >> 2);
  x |= (x >> 4);
  x |= (x >> 8);
  x |= (x >> 16);

  return (ones(x) - 1 - y);
}

static inline
__attribute__ ((unused))
void gc_clear_block
  (const gc_value block, const size_t size, const size_t full_size)
{
  size_t i;
  for (i = size; i < full_size; i++)
    SET_NTH_FIELD(block, i, NULL);
  return;
}

//

static inline
__attribute__ ((unused))
gc_value gc_alloc_atomic_word(const size_t size)
{
  unsigned int log_size;
  gc_value temp;

  if (size >= LARGEST_BLOCK_SIZE_IN_CHUNK)
    return gc_big_alloc_word(size, 1);

  log_size = ceil_log2(size);
  if (atomic_free_lists[log_size] == NULL)
    atomic_free_lists[log_size] = gc_refresh_atomic_freelist(log_size);
  temp = atomic_free_lists[log_size];
  atomic_free_lists[log_size] = *((gc_value *)temp);

  return (gc_value)temp;
}

static inline
__attribute__ ((unused))
gc_value gc_alloc_atomic_byte(const size_t size)
{
  int wsz = (size + BYTES_PER_WORD - 1) >> BYTES_PER_WORD_LOG;
  return gc_alloc_atomic_word(wsz) ;
}

static inline
__attribute__ ((unused))
gc_value gc_alloc_word(const size_t size)
{
  unsigned int log_size;
  gc_value temp;

  if (size >= LARGEST_BLOCK_SIZE_IN_CHUNK)
    return gc_big_alloc_word(size, 0);

  log_size = ceil_log2(size);
  if (free_lists[log_size] == NULL)
    free_lists[log_size] = gc_refresh_freelist(log_size);
  temp = free_lists[log_size];
  free_lists[log_size] = *((gc_value *)temp);
  gc_clear_block(temp, size, 1 << log_size);

  return temp;
}

static inline
__attribute__ ((unused))
gc_value gc_alloc_byte(const size_t size)
{
  int wsz = (size + BYTES_PER_WORD - 1) >> BYTES_PER_WORD_LOG;
  return gc_alloc_word(wsz) ;
}

static inline
__attribute__ ((unused))
gc_value gc_alloc_byte_zero(const size_t size)
{
  int wsz = (size + BYTES_PER_WORD - 1) >> BYTES_PER_WORD_LOG;
  gc_value p = gc_alloc_word(wsz) ;
/*
  fprintf(stdout, "gc_alloc_byte_zero: memset\n") ;
*/
  memset(p, 0, wsz) ;
  return p ;
}

#endif /* _ATS_GC_H_ */
