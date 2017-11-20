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

#ifndef _GNU_SOURCE
#define _GNU_SOURCE /* Needed for posix_memalign */
#endif

#ifdef ATS_MULTITHREAD
#include <pthread.h>
#include <semaphore.h>
#endif

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <memory.h>
#include <signal.h>
#include <setjmp.h>
#include <errno.h>

#include "gc.h"

#define CHUNK_WORD_SIZE (1 << CHUNK_WORD_SIZE_LOG)
#define CHUNK_BYTE_SIZE_LOG (CHUNK_WORD_SIZE_LOG+BYTES_PER_WORD_LOG)
#define CHUNK_BYTE_SIZE (1 << CHUNK_BYTE_SIZE_LOG)
#define BOTTOM_LEVEL_SIZE_LOG 10
#define BOTTOM_LEVEL_SIZE (1 << BOTTOM_LEVEL_SIZE_LOG)
#define TOP_LEVEL_SIZE_LOG (BITS_PER_WORD-BOTTOM_LEVEL_SIZE_LOG-CHUNK_BYTE_SIZE_LOG)
#define TOP_LEVEL_SIZE (1 << TOP_LEVEL_SIZE_LOG)

#define NUM_SIZE_BINS (LARGEST_BLOCK_SIZE_IN_CHUNK_LOG+1)

#define MARK_STACK_ENTRIES_PER_PAGE 4095
#define MARK_STACK_CUTOFF (LARGEST_BLOCK_SIZE_IN_CHUNK / 4)

#define CHUNKS_PER_MARK_STACK_PAGES 32
 
#define SWEEP_CONSIDERATION_CUTOFF_DIVIDER 2

#define SET_MARK(x, i) do { ((x)[i / 8] |= (1 << (i % 8))); } while (0)
#define CLEAR_MARK(x, i) do { ((x)[i / 8] &= ~(1 << (i % 8))); } while (0)
#define IS_MARK_SET(x, i) (((x)[i / 8] >> (i % 8)) & 0x1)

#define SPLIT_PTR_CHUNK(a, b) do { (b) = ((a) & (CHUNK_BYTE_SIZE-1)) >> BYTES_PER_WORD_LOG; } while (0)
#define SPLIT_PTR_NO_CHUNK(a, b, c) \
  do { \
     (b) = (a) >> (CHUNK_BYTE_SIZE_LOG+BOTTOM_LEVEL_SIZE_LOG); \
     (c) = ((a) >> CHUNK_BYTE_SIZE_LOG) & (BOTTOM_LEVEL_SIZE-1); \
  } while (0)
#define SPLIT_PTR(a, b, c, d) do { SPLIT_PTR_NO_CHUNK(a, b, c); SPLIT_PTR_CHUNK(a, d); } while (0)

#define INITIAL_BYTE_LIMIT CHUNK_BYTE_SIZE
// #define INITIAL_BYTE_LIMIT (32 * 1024)
#define INITIAL_CHUNK_LIMIT (INITIAL_BYTE_LIMIT / CHUNK_BYTE_SIZE)

typedef struct chunk_header_struct {
  unsigned char is_atomic;
  unsigned char element_size_log;
#ifdef ATS_MULTITHREAD
  unsigned char on_free_list;
#endif
  unsigned short mark_counter;
  size_t num_mark_blocks;
  size_t element_size;
  struct chunk_header_struct* sweep_next;
  gc_value chunk_ptr;
  unsigned char mark_bits[];
} chunk_header;

typedef struct bottom_level_table_struct {
  chunk_header* chunk_headers[BOTTOM_LEVEL_SIZE];
#if (__WORDSIZE == 64)
  uintptr_t key;
  struct bottom_level_table_struct* hash_next;
#endif
} bottom_level_table;

typedef struct mark_stack_entry_struct {
  gc_value data;
  size_t size;
} mark_stack_entry;

typedef struct mark_stack_page_struct {
  struct mark_stack_page_struct* next;
  struct mark_stack_page_struct* prev;
  mark_stack_entry entries[MARK_STACK_ENTRIES_PER_PAGE];
} mark_stack_page;

typedef struct global_root_struct {
  gc_value* data;
  size_t size;
  struct global_root_struct* next;
} global_root;

typedef struct persistant_header_struct {
  size_t size;
  struct persistant_header_struct* next;
  struct persistant_header_struct* prev;
  gc_value data[];
} persistant_header;

#ifdef ATS_MULTITHREAD
typedef struct thread_descriptor_struct {
  pthread_t thread_pid;
  void* stack_begin;
  void* stack_end;
  struct thread_descriptor_struct* next;
  struct thread_descriptor_struct* prev;
} thread_descriptor;

static sem_t sleep_sem;
static pthread_mutex_t descriptors_mutex = PTHREAD_MUTEX_INITIALIZER;
static thread_descriptor* thread_descriptors = NULL;
static __thread thread_descriptor* current_thread = NULL;
#endif

#if (__WORDSIZE == 32)
static bottom_level_table* top_level[TOP_LEVEL_SIZE] = { NULL };
#elif (__WORDSIZE == 64)
static bottom_level_table* top_level[TOP_LEVEL_HASH_SIZE] = { NULL };
#endif

static mark_stack_page* mark_stack_head = NULL;
static mark_stack_page* mark_stack_current = NULL;
static unsigned int mark_stack_pos = 0;
static unsigned int mark_stack_num_pages = 0;
static unsigned int mark_stack_overflowed = 0;

#ifdef ATS_MULTITHREAD
static pthread_mutex_t sweep_lists_lock[NUM_SIZE_BINS] = { PTHREAD_MUTEX_INITIALIZER };
static pthread_mutex_t atomic_sweep_lists_lock[NUM_SIZE_BINS] = { PTHREAD_MUTEX_INITIALIZER };
static pthread_mutex_t global_root_list_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t persistant_list_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t free_list_lock = PTHREAD_MUTEX_INITIALIZER;

static __thread chunk_header* free_list_headers[NUM_SIZE_BINS] = { NULL };
static __thread chunk_header* atomic_free_list_headers[NUM_SIZE_BINS] = { NULL };
#endif

static chunk_header* sweep_lists[NUM_SIZE_BINS] = { NULL };
static chunk_header* atomic_sweep_lists[NUM_SIZE_BINS] = { NULL };

#ifdef ATS_MULTITHREAD
__thread gc_value free_lists[NUM_SIZE_BINS] = { NULL };
__thread gc_value atomic_free_lists[NUM_SIZE_BINS] = { NULL };
#else
gc_value free_lists[NUM_SIZE_BINS] = { NULL };
gc_value atomic_free_lists[NUM_SIZE_BINS] = { NULL };
#endif

static gc_value free_chunk_list = NULL;

static global_root* global_root_list = NULL;
static persistant_header* persistant_list = NULL;

static size_t chunk_count = 0;
static size_t chunk_limit = INITIAL_CHUNK_LIMIT;

static int stack_direction = 0;
#ifndef ATS_MULTITHREAD
static void* stack_begin = NULL;
#endif

#ifdef ATS_MULTITHREAD
void handle_SIGUSR1(int signum)
{
  sigset_t new_sigset;
  jmp_buf reg_save;

  current_thread->stack_end = &reg_save;

  setjmp(reg_save);
  asm volatile ("": : :"memory");

  sem_post(&sleep_sem);

  sigfillset(&new_sigset);
  sigdelset(&new_sigset, SIGUSR2);
  sigsuspend(&new_sigset);

  return;
}

void handle_SIGUSR2(int signum)
{
  return;
}
#endif

static int volatile gc_get_stack_direction(unsigned int* some_ptr)
{
  unsigned int some_int = 0;

  if (some_ptr == NULL)
    return gc_get_stack_direction(&some_int);
  else {
    if (&some_int > some_ptr) return 1;
    else return -1;
  }
}

static void* gc_get_stack_begin()
{
  long page_size;

  page_size = sysconf(_SC_PAGESIZE);

  if (stack_direction < 0)
    return (void*)(((((uintptr_t)(&page_size)) + page_size) & ~(page_size-1))-1);
  else
    return (void*)((uintptr_t)(&page_size) & ~(page_size-1));
}

#ifdef ATS_MULTITHREAD
static void gc_init_thread_descriptor()
{
  thread_descriptor* current;

  current = (thread_descriptor*)malloc(sizeof(thread_descriptor));
  if (current == NULL) {
    perror("Unable to malloc thread descriptor!\n");
    exit(1);
  }

  current->thread_pid = pthread_self();
  current->stack_begin = gc_get_stack_begin();
  current_thread = current;

  pthread_mutex_lock(&descriptors_mutex);
  current->next = thread_descriptors;
  current->prev = NULL;
  if (thread_descriptors != NULL)
    thread_descriptors->prev = current;
  thread_descriptors = current;
  pthread_mutex_unlock(&descriptors_mutex);

  return;
}

static void gc_thread_cleanup(void* arg)
{
  pthread_mutex_lock(&descriptors_mutex);

  if (thread_descriptors == current_thread) {
    thread_descriptors = thread_descriptors->next;
    if (thread_descriptors != NULL)
      thread_descriptors->prev = NULL;
  } else {
    current_thread->prev->next = current_thread->next;
    if (current_thread->next != NULL)
      current_thread->next->prev = current_thread->prev;
  }

  pthread_mutex_unlock(&descriptors_mutex);

  free(current_thread);
  current_thread = NULL;

  return;
}

void* gc_thread_stub(void* stub)
{
  void *(*start_routine)(void*);
  void* arg;
  void* ret;
  void** ret_stub;
  int is_detached;

  start_routine = (void*(*)(void*))((void**)stub)[0];
  arg = ((void**)stub)[1];
  is_detached = (int)((void**)stub)[2];

  if (is_detached)
    pthread_detach(pthread_self());

  gc_free_persistant((gc_value)stub);

  gc_init_thread_descriptor();

  pthread_cleanup_push(gc_thread_cleanup, NULL);
  ret = start_routine(arg);
  pthread_cleanup_pop(1);

  if (is_detached)
    return NULL;
  else {
    ret_stub = gc_allocate_persistant_word(1);
    if (ret_stub == NULL) {
      perror("Unable to allocate return value stub!\n");
      exit(1);
    }
    ret_stub[0] = ret;
    return ret_stub;
  }
}

int gc_create_pthread (
  void *(*start_routine)(void*), void *arg, pthread_t* pid, int detached
) {
  void** data_stub;
  pthread_t pid2;
  int ret;

  data_stub = gc_allocate_persistant_word(3);
  if (data_stub == NULL) {
    perror("Unable to allocate data stub!\n");
    exit(1);
  }

  data_stub[0] = (void*)start_routine;
  data_stub[1] = arg;
  data_stub[2] = (void*)detached;

  ret = pthread_create(&pid2, NULL, gc_thread_stub, data_stub);
  if (ret != 0)
    gc_free_persistant(data_stub);

  if (pid != NULL)
    *pid = pid2;

  return ret;
}

static void gc_init_signals()
{
  struct sigaction new_action1, new_action2;

  new_action1.sa_handler = handle_SIGUSR1;
  sigemptyset(&new_action1.sa_mask);
  sigaddset(&new_action1.sa_mask, SIGUSR2);
  new_action1.sa_flags = SA_RESTART;

  if (sigaction(SIGUSR1, &new_action1, NULL) < 0)
    perror("sigaction is bad!\n");

  new_action2.sa_handler = handle_SIGUSR2;
  sigemptyset(&new_action2.sa_mask);
  sigaddset(&new_action2.sa_mask, SIGUSR1);
  new_action2.sa_flags = SA_RESTART;

  if (sigaction(SIGUSR2, &new_action2, NULL) < 0)
    perror("sigaction is bad!\n");

  return;
}
#endif

gc_value gc_allocate_persistant_byte(const size_t size)
{
  persistant_header* block;

  block = (persistant_header*)malloc(sizeof(persistant_header)+size);
  if (!block) return NULL; // Emulate malloc's semantics
  
  memset(block->data, 0, size);
  block->size = size >> BYTES_PER_WORD_LOG;
  block->prev = NULL;

#ifdef ATS_MULTITHREAD
  pthread_mutex_lock(&persistant_list_lock);
#endif

  if (persistant_list != NULL)
    persistant_list->prev = block;
  block->next = persistant_list;
  persistant_list = block;
  
#ifdef ATS_MULTITHREAD
  pthread_mutex_unlock(&persistant_list_lock);
#endif

  return (gc_value)block->data;
}

gc_value gc_allocate_persistant_word(const size_t size) {
  return gc_allocate_persistant_byte (size << BYTES_PER_WORD_LOG) ;
}

void gc_free_persistant(gc_value ptr)
{
  persistant_header* block;

  block = (persistant_header*)((char*)ptr - offsetof(persistant_header, data));

#ifdef ATS_MULTITHREAD
  pthread_mutex_lock(&persistant_list_lock);
#endif

  if (!block->prev)
    persistant_list = block->next;
  else
    block->prev->next = block->next;

  if (block->next)
    block->next->prev = block->prev;

#ifdef ATS_MULTITHREAD
  pthread_mutex_unlock(&persistant_list_lock);
#endif

  free(block);

  return;
}

// The following function is added by Hongwei Xi (June 2007)
gc_value gc_reallocate_persistant_byte(const gc_value ptr, const size_t size)
{
  persistant_header* block;

  block = (persistant_header*)((char*)ptr - offsetof(persistant_header, data));

#ifdef ATS_MULTITHREAD
  pthread_mutex_lock(&persistant_list_lock);
#endif

  block = (persistant_header*)realloc(block, sizeof(persistant_header)+size);
  if (!block) return NULL; // Emulate realloc's semantics

  if (!block->prev)
    persistant_list = block;
  else
    block->prev->next = block;

  if (block->next)
    block->next->prev = block;

#ifdef ATS_MULTITHREAD
  pthread_mutex_unlock(&persistant_list_lock);
#endif

  return (gc_value)block->data;
}

//

void gc_markroot(gc_value* ptr, size_t sz)
{
  global_root* root;

  root = (global_root*)malloc(sizeof(global_root));
  if (root == NULL) {
    fprintf(stderr, "GC FATAL ERROR! Unable to allocate memory for a global root marker!\n");
    exit(1);
  }

  root->data = ptr; root->size = sz;

#ifdef ATS_MULTITHREAD
  pthread_mutex_lock(&global_root_list_lock);
#endif

  root->next = global_root_list;
  global_root_list = root;

#ifdef ATS_MULTITHREAD
  pthread_mutex_unlock(&global_root_list_lock);
#endif

  return;
}

static void gc_extend_mark_stack(const unsigned int pages)
{
  unsigned int i;
  mark_stack_page* temp;

  for (i = 0; i < pages; i++) {
    temp = (mark_stack_page*)malloc(sizeof(mark_stack_page));
    if (temp == NULL) {
      fprintf(stderr, "GC FATAL ERROR! Unable to allocate memory for a mark stack page!\n");
      exit(1);
    }
    if (mark_stack_head != NULL)
      mark_stack_head->prev = temp;
    temp->next = mark_stack_head;
    temp->prev = NULL;
    mark_stack_head = temp;
  }

  mark_stack_current = mark_stack_head;
  mark_stack_num_pages += pages;

  return;
}

static void gc_push_mark_stack(gc_value ptr, const size_t size)
{
  mark_stack_current->entries[mark_stack_pos].data = ptr;
  mark_stack_current->entries[mark_stack_pos].size = size;

  mark_stack_pos++;
  if (mark_stack_pos == MARK_STACK_ENTRIES_PER_PAGE) {
    if (mark_stack_current->next == NULL) {
      mark_stack_overflowed = 1;
      mark_stack_pos--;
    } else {
      mark_stack_pos = 0;
      mark_stack_current = mark_stack_current->next;
    }
  }
  
  return;
}

static void gc_pop_mark_stack(gc_value* output_ptr, size_t* output_size)
{
  if (mark_stack_pos == 0) {
    if (mark_stack_current->prev == NULL) {
      *output_ptr = NULL;
      return;
    }
    mark_stack_current = mark_stack_current->prev;
    *output_ptr = mark_stack_current->entries[MARK_STACK_ENTRIES_PER_PAGE-1].data;
    *output_size = mark_stack_current->entries[MARK_STACK_ENTRIES_PER_PAGE-1].size;
    mark_stack_pos = MARK_STACK_ENTRIES_PER_PAGE-1;
    return;
  }

  mark_stack_pos--;
  *output_ptr = mark_stack_current->entries[mark_stack_pos].data;
  *output_size = mark_stack_current->entries[mark_stack_pos].size;
  
  return;
}

static void gc_make_chunk_visible(gc_value ptr, chunk_header* chunk_hdr)
{
  uintptr_t bottom_offset, top_offset;
#if (__WORDSIZE == 64)
  bottom_level_table* temp;
#endif

  SPLIT_PTR_NO_CHUNK((uintptr_t)ptr, top_offset, bottom_offset);

#if (__WORDSIZE == 32)
  if (top_level[top_offset] == NULL) {
    top_level[top_offset] = (bottom_level_table*)calloc(1, sizeof(bottom_level_table));
    if (top_level[top_offset] == NULL) {
      fprintf(stderr, "GC FATAL ERROR! Unable to allocate a bottom level table entry!\n");
      exit(1);
    }
  }
  top_level[top_offset]->chunk_headers[bottom_offset] = chunk_hdr;
#elif (__WORDSIZE == 64)
  temp = top_level[top_offset % TOP_LEVEL_HASH_SIZE];
  while (temp != NULL && temp->key != top_offset)
    temp = temp->hash_next;
  if (temp == NULL) {
    temp = (bottom_level_table*)calloc(1, sizeof(bottom_level_table));
    if (temp == NULL) {
      fprintf(stderr, "GC FATAL ERROR! Unable to allocate a bottom level table entry!\n");
      exit(1);
    }
    temp->key = top_offset;
    temp->hash_next = top_level[top_offset % TOP_LEVEL_HASH_SIZE];
    top_level[top_offset % TOP_LEVEL_HASH_SIZE] = temp;
  }
  temp->chunk_headers[bottom_offset] = chunk_hdr;
#endif
 
  return;
}

static void gc_zap_chunk_from_table(gc_value ptr)
{
  uintptr_t bottom_offset, top_offset;
#if (__WORDSIZE == 64)
  bottom_level_table* temp;
#endif

  SPLIT_PTR_NO_CHUNK((uintptr_t)ptr, top_offset, bottom_offset);

#if (__WORDSIZE == 32)
  top_level[top_offset]->chunk_headers[bottom_offset] = NULL;
#elif (__WORDSIZE == 64)
  temp = top_level[top_offset % TOP_LEVEL_HASH_SIZE];
  while (temp->key != top_offset)
    temp = temp->hash_next;
  temp->chunk_headers[bottom_offset] = NULL;
#endif

  return;
}

void gc_destroy_chunk(chunk_header* chunk_hdr)
{
  gc_zap_chunk_from_table(chunk_hdr->chunk_ptr);

  if (chunk_hdr->element_size > LARGEST_BLOCK_SIZE_IN_CHUNK) {
    free(chunk_hdr->chunk_ptr);
    chunk_count -= (chunk_hdr->element_size + CHUNK_WORD_SIZE - 1) / CHUNK_WORD_SIZE;
  } else {
    *(chunk_hdr->chunk_ptr) = (gc_value)free_chunk_list;
    free_chunk_list = chunk_hdr->chunk_ptr;
    chunk_count--;
  }

  free(chunk_hdr);

  return;
}

static chunk_header* gc_is_ptr_valid(gc_value ptr, size_t* out_offset)
{
  uintptr_t chunk_offset, bottom_offset, top_offset;
  bottom_level_table* bottom_level;
  chunk_header* chunk;

  if (ptr == NULL || ((uintptr_t)ptr % BYTES_PER_WORD) != 0)
    return NULL;

  SPLIT_PTR((uintptr_t)ptr, top_offset, bottom_offset, chunk_offset);

#if (__WORDSIZE == 32)
  bottom_level = top_level[top_offset];
#elif (__WORDSIZE == 64)
  bottom_level = top_level[top_offset % TOP_LEVEL_HASH_SIZE];
  while (bottom_level != NULL && bottom_level->key != top_offset)
    bottom_level = bottom_level->hash_next;
#endif

  if (bottom_level == NULL)
    return NULL;
  chunk = bottom_level->chunk_headers[bottom_offset];
  if (chunk == NULL || (chunk_offset & ((1 << chunk->element_size_log)-1)) != 0)
    return NULL;
  *out_offset = (chunk_offset >> chunk->element_size_log);
  return chunk;
}

static void gc_do_mark(gc_value ptr)
{
  unsigned int i;
  size_t element_size, chunk_offset;
  chunk_header* chunk_hdr;
  gc_value candidate;

  chunk_hdr = gc_is_ptr_valid(ptr, &chunk_offset);
  if (!chunk_hdr || IS_MARK_SET(chunk_hdr->mark_bits, chunk_offset))
    return;

  SET_MARK(chunk_hdr->mark_bits, chunk_offset);
  chunk_hdr->mark_counter++;

  if (chunk_hdr->is_atomic)
    return;
  
  element_size = chunk_hdr->element_size;

  while (ptr != NULL) {
    if (element_size > MARK_STACK_CUTOFF) {
      gc_push_mark_stack(ptr + MARK_STACK_CUTOFF, element_size - MARK_STACK_CUTOFF);
      element_size = MARK_STACK_CUTOFF;
    }
    for (i = 0; i < element_size-1; i++) {
      candidate = ((gc_value *)ptr)[i];
      chunk_hdr = gc_is_ptr_valid(candidate, &chunk_offset);
      if (chunk_hdr && !IS_MARK_SET(chunk_hdr->mark_bits, chunk_offset)) {
	SET_MARK(chunk_hdr->mark_bits, chunk_offset);
	chunk_hdr->mark_counter++;
	if (!chunk_hdr->is_atomic)
	  gc_push_mark_stack(candidate, chunk_hdr->element_size);
      }
    }
    candidate = ((gc_value *)ptr)[element_size-1];
    chunk_hdr = gc_is_ptr_valid(candidate, &chunk_offset);
    if (chunk_hdr && !IS_MARK_SET(chunk_hdr->mark_bits, chunk_offset)) {
      SET_MARK(chunk_hdr->mark_bits, chunk_offset);
      chunk_hdr->mark_counter++;
      if (!chunk_hdr->is_atomic) {
	ptr = candidate;
	element_size = chunk_hdr->element_size;
      } else
	gc_pop_mark_stack(&ptr, &element_size);
    } else
      gc_pop_mark_stack(&ptr, &element_size);
  }

  return;
}

static void gc_do_catastrophic_mark_chunk(chunk_header* chunk_hdr)
{
  int i, j;

  for (i = 0; i < (CHUNK_WORD_SIZE >> chunk_hdr->element_size_log); i++) {
    if (IS_MARK_SET(chunk_hdr->mark_bits, i)) {
      for (j = 0; j < (1 << chunk_hdr->element_size_log); j++)
	gc_do_mark(*(chunk_hdr->chunk_ptr + (i << chunk_hdr->element_size_log) + j));
    }
  }

  return;
}

static void gc_do_catastrophic_mark_bottom(bottom_level_table* bottom_level)
{
  chunk_header* chunk_hdr;
  unsigned int i;

  for (i = 0; i < BOTTOM_LEVEL_SIZE; i++) {
    chunk_hdr = bottom_level->chunk_headers[i];
    if (chunk_hdr != NULL)
      gc_do_catastrophic_mark_chunk(chunk_hdr);
  }
  
  return;
}

static void gc_do_catastrophic_mark()
{
  unsigned int i;
#if (__WORDSIZE == 64)
  bottom_level_table* temp;
#endif

#if (__WORDSIZE == 32)
  for (i = 0; i < TOP_LEVEL_SIZE; i++) {
    if (top_level[i] != NULL)
      gc_do_catastrophic_mark_bottom(top_level[i]);
  }
#elif (__WORDSIZE == 64)
  for (i = 0; i < TOP_LEVEL_HASH_SIZE; i++) {
    temp = top_level[i];
    while (temp != NULL) {
      gc_do_catastrophic_mark_bottom(temp);
      temp = temp->hash_next;
    }
  }
#endif

  return;
}

static
unsigned int
gc_thread_chunk
  (gc_value chunk, const unsigned int element_size_log, unsigned char* mark_bits)
{
  int i, isz;
  unsigned int prev_index;
  gc_value prev = NULL;

  prev_index = CHUNK_WORD_SIZE;
  for (i = (CHUNK_WORD_SIZE >> element_size_log)-1; i >= 0; i--) {
    if (!IS_MARK_SET(mark_bits, i)) {
      isz = i << element_size_log;
      ((gc_value *)chunk)[isz] = prev;
      prev = (gc_value)((gc_value *)chunk + isz);
      prev_index = isz;
    } 
  }
  return prev_index;
}

static void gc_clear_marks_bottom(bottom_level_table* bottom_level)
{
  chunk_header* chunk_hdr;
  unsigned int i;

  for (i = 0; i < BOTTOM_LEVEL_SIZE; i++) {
    chunk_hdr = bottom_level->chunk_headers[i];
    if (chunk_hdr != NULL) {
      chunk_hdr->mark_counter = 0;
      memset(chunk_hdr->mark_bits, 0, chunk_hdr->num_mark_blocks*sizeof(unsigned char));
    }
  }

  return;
}

static void gc_clear_marks()
{
  unsigned int i;

#if (__WORDSIZE == 32)
  for (i = 0; i < TOP_LEVEL_SIZE; i++) {
    if (top_level[i] != NULL)
      gc_clear_marks_bottom(top_level[i]);
  }
#elif (__WORDSIZE == 64)
  bottom_level_table* temp;
  for (i = 0; i < TOP_LEVEL_HASH_SIZE; i++) {
    temp = top_level[i];
    while (temp != NULL) {
      gc_clear_marks_bottom(temp);
      temp = temp->hash_next;
    }
  }
#endif

  return;
}

static void gc_build_sweep_lists_bottom(bottom_level_table* bottom_level)
{
  unsigned int i;
  chunk_header* chunk_hdr;

#ifdef ATS_MULTITHREAD
#define OPT_CHECK (chunk_hdr->on_free_list == 0)
#else
#define OPT_CHECK (1)
#endif

  for (i = 0; i < BOTTOM_LEVEL_SIZE; i++) {
    chunk_hdr = bottom_level->chunk_headers[i];
    if (chunk_hdr && OPT_CHECK) {
      if (chunk_hdr->mark_counter == 0) {
	gc_destroy_chunk(chunk_hdr);
      } else if (chunk_hdr->element_size <= LARGEST_BLOCK_SIZE_IN_CHUNK &&
		 chunk_hdr->mark_counter < (unsigned int)((1 << (CHUNK_WORD_SIZE_LOG - chunk_hdr->element_size_log))
							  / SWEEP_CONSIDERATION_CUTOFF_DIVIDER)) {
	if (chunk_hdr->is_atomic) {
	  chunk_hdr->sweep_next = atomic_sweep_lists[chunk_hdr->element_size_log];
	  atomic_sweep_lists[chunk_hdr->element_size_log] = chunk_hdr;
	} else {
	  chunk_hdr->sweep_next = sweep_lists[chunk_hdr->element_size_log];
	  sweep_lists[chunk_hdr->element_size_log] = chunk_hdr;
	}
      }
    }
  }

  return;
}

static void gc_build_sweep_lists()
{
  unsigned int i;
#if (__WORDSIZE == 64)
  bottom_level_table* temp;
#endif

  for (i = 0; i < NUM_SIZE_BINS; i++)
    sweep_lists[i] = NULL;
  for (i = 0; i < NUM_SIZE_BINS; i++)
    atomic_sweep_lists[i] = NULL;

#if (__WORDSIZE == 32)
  for (i = 0; i < TOP_LEVEL_SIZE; i++) {
    if (top_level[i] != NULL)
      gc_build_sweep_lists_bottom(top_level[i]);
  }
#elif (__WORDSIZE == 64)
  for (i = 0; i < TOP_LEVEL_HASH_SIZE; i++) {
    temp = top_level[i];
    while (temp != NULL) {
      gc_build_sweep_lists_bottom(temp);
      temp = temp->hash_next;
    }
  }
#endif

  return;
}

static void gc_unmark_free_lists()
{
  unsigned int i;
  size_t chunk_offset;
  gc_value temp;
  chunk_header* chunk_hdr;

  for (i = 0; i < NUM_SIZE_BINS; i++) {
    temp = (gc_value)free_lists[i];
    while (temp != NULL) {
      chunk_hdr = gc_is_ptr_valid(temp, &chunk_offset);
      if (chunk_hdr && IS_MARK_SET(chunk_hdr->mark_bits, chunk_offset)) {
	chunk_hdr->mark_counter--;
	CLEAR_MARK(chunk_hdr->mark_bits, chunk_offset);
      }
      temp = *((gc_value*)temp);
    }
  }

  for (i = 0; i < NUM_SIZE_BINS; i++) {
    temp = (gc_value)atomic_free_lists[i];
    while (temp != NULL) {
      chunk_hdr = gc_is_ptr_valid(temp, &chunk_offset);
      if (chunk_hdr && IS_MARK_SET(chunk_hdr->mark_bits, chunk_offset)) {
        chunk_hdr->mark_counter--;
        CLEAR_MARK(chunk_hdr->mark_bits, chunk_offset);
      }
      temp = *((gc_value*)temp);
    }
  }

  for (i = 0; i < NUM_SIZE_BINS; i++)
    free_lists[i] = NULL;
  for (i = 0; i < NUM_SIZE_BINS; i++)
    atomic_free_lists[i] = NULL;

#ifdef ATS_MULTITHREAD
  for (i = 0; i < NUM_SIZE_BINS; i++) {
    if (free_list_headers[i] != NULL) {
      free_list_headers[i]->on_free_list = 0;
      free_list_headers[i] = NULL;
    }
  }

  for (i = 0; i < NUM_SIZE_BINS; i++) {
    if (atomic_free_list_headers[i] != NULL) {
      atomic_free_list_headers[i]->on_free_list = 0;
      atomic_free_list_headers[i] = NULL;
    }
  }
#endif

  return;
}

static int gc_do_mark_phase()
{
  unsigned int i;
  persistant_header* temp_persistant;
  global_root* temp; int sz; gc_value* data;
  gc_value* begin;
  gc_value* end;
#ifdef ATS_MULTITHREAD
  thread_descriptor* temp_thread;
#endif
  int overflow_happened;

  mark_stack_overflowed = 0;

  temp_persistant = persistant_list;
  while (temp_persistant != NULL) {
    for (i = 0; i < temp_persistant->size; i++)
      gc_do_mark(temp_persistant->data[i]);
    temp_persistant = temp_persistant->next;
  }

  temp = global_root_list;
  while (temp != NULL) {
    sz = temp->size; data = temp->data;
    for (i = 0; i + sizeof(gc_value) <= sz; i += sizeof(gc_value)) {
      gc_do_mark(*data); ++data;
    }
    temp = temp->next;
  }

  if (stack_direction < 0) {
    begin = (gc_value*)&overflow_happened;
#ifdef ATS_MULTITHREAD
    end = (gc_value*)current_thread->stack_begin;
#else
    end = (gc_value*)stack_begin;
#endif
  } else {
#ifdef ATS_MULTITHREAD
    begin = (gc_value*)current_thread->stack_begin;
#else
    begin = (gc_value*)stack_begin;
#endif
    end = (gc_value*)&overflow_happened;
  }

  while (begin <= end) {
    gc_do_mark(*begin);
    begin++;
  }

#ifdef ATS_MULTITHREAD
  temp_thread = thread_descriptors;
  while (temp_thread != NULL) {
    if (pthread_equal(current_thread->thread_pid, temp_thread->thread_pid) == 0) {
      if (stack_direction < 0) {
	begin = (gc_value*)temp_thread->stack_end;
	end = (gc_value*)temp_thread->stack_begin;
      } else {
	begin = (gc_value*)temp_thread->stack_begin;
	end = (gc_value*)temp_thread->stack_end;
      }
      while (begin <= end) {
	gc_do_mark((gc_value)*begin);
	begin++;
      }
    }
    temp_thread = temp_thread->next;
  }
#endif

  overflow_happened = mark_stack_overflowed;
  while (mark_stack_overflowed) {
    mark_stack_overflowed = 0;
    gc_do_catastrophic_mark();
  }

  return overflow_happened;
}

static void gc_collect()
{
  jmp_buf reg_save;
  int needed_mark_pages, overflow_happened;
#ifdef ATS_MULTITHREAD
  thread_descriptor* temp;
#endif

  /*
  fprintf(
    stderr
  , "GC begins: chunk_count = %i and chunk_limit = %i\n"
  , chunk_count
  , chunk_limit
  ) ;
  */

  setjmp(reg_save);
  asm volatile ("": : :"memory");

  needed_mark_pages = (((CHUNK_WORD_SIZE*chunk_count)+((MARK_STACK_ENTRIES_PER_PAGE*CHUNKS_PER_MARK_STACK_PAGES-1)))/
		       (MARK_STACK_ENTRIES_PER_PAGE*CHUNKS_PER_MARK_STACK_PAGES)) - mark_stack_num_pages;
  if (needed_mark_pages > 0)
    gc_extend_mark_stack(needed_mark_pages);

  gc_clear_marks();

#ifdef ATS_MULTITHREAD
  temp = thread_descriptors;
  while (temp != NULL) {
    if (pthread_equal(current_thread->thread_pid, temp->thread_pid) == 0)
      pthread_kill(temp->thread_pid, SIGUSR1);
    temp = temp->next;
  }
  temp = thread_descriptors;
  while (temp != NULL) {
    if (pthread_equal(current_thread->thread_pid, temp->thread_pid) == 0)
      sem_wait(&sleep_sem);
    temp = temp->next;
  }
#endif

  overflow_happened = gc_do_mark_phase();
 
#ifdef ATS_MULTITHREAD
  temp = thread_descriptors;
  while (temp != NULL) {
    if (pthread_equal(current_thread->thread_pid, temp->thread_pid) == 0)
      pthread_kill(temp->thread_pid, SIGUSR2);
    temp = temp->next;
  }
#endif

  gc_unmark_free_lists();
  gc_build_sweep_lists();

  if (overflow_happened)
    gc_extend_mark_stack(2);

  /*
  fprintf(
    stderr
  , "GC ends: chunk_count = %i and chunk_limit = %i\n"
  , chunk_count
  , chunk_limit
  ) ;
  */

  return;
}

static gc_value gc_create_chunk
  (const unsigned int is_atomic, const unsigned int element_size_log, const size_t element_size)
{
  size_t num_mark_blocks, chunk_size, i;
  chunk_header* chunk_hdr;
  gc_value chunk = NULL;

  num_mark_blocks = ((CHUNK_WORD_SIZE >> element_size_log) + 7) / 8;
  
  if (element_size > LARGEST_BLOCK_SIZE_IN_CHUNK)
    chunk_size = element_size*sizeof(gc_value);
  else
    chunk_size = CHUNK_BYTE_SIZE;

  chunk_hdr = (chunk_header*)malloc(sizeof(chunk_header)+num_mark_blocks);
  if (chunk_hdr == NULL) {
    fprintf(stderr, "GC FATAL ERROR! Unable to allocate header for a chunk!\n");
    exit(1);
  }

  chunk_hdr->is_atomic = is_atomic;
  chunk_hdr->num_mark_blocks = num_mark_blocks;
  chunk_hdr->element_size = element_size;
  chunk_hdr->element_size_log = element_size_log;
  chunk_hdr->mark_counter = 0;
#ifdef ATS_MULTITHREAD
  if (element_size > LARGEST_BLOCK_SIZE_IN_CHUNK)
    chunk_hdr->on_free_list = 0;
  else {
    chunk_hdr->on_free_list = 1;
    if (is_atomic)
      atomic_free_list_headers[element_size_log] = chunk_hdr;
    else
      free_list_headers[element_size_log] = chunk_hdr;
  }
#endif
  chunk_hdr->sweep_next = NULL;

  if (free_chunk_list == NULL || element_size > LARGEST_BLOCK_SIZE_IN_CHUNK) {
    if (posix_memalign((void**)(&chunk), CHUNK_BYTE_SIZE, chunk_size) != 0) {
      fprintf(stderr, "GC FATAL ERROR! Unable to allocate a chunk!\n");
      exit(1);
    }
  } else {
    chunk = free_chunk_list;
    free_chunk_list = *((gc_value*)chunk);
  }

  chunk_hdr->chunk_ptr = chunk;

  if (element_size > LARGEST_BLOCK_SIZE_IN_CHUNK)
    *((gc_value *)chunk) = NULL;
  else {
    for (i = 0; i+element_size < CHUNK_WORD_SIZE; i+=element_size)
      ((gc_value *)chunk)[i] = (gc_value)((gc_value*)chunk)+i+element_size;
    ((gc_value *)chunk)[i] = NULL;
  }
 
  gc_make_chunk_visible(chunk, chunk_hdr);

  return chunk;
}

void gc_init()
{
  unsigned int i;
  
  stack_direction = gc_get_stack_direction(&i);

#ifdef ATS_MULTITHREAD
  sem_init(&sleep_sem, 0, 0);
  gc_init_thread_descriptor();
  gc_init_signals();
#else
  stack_begin = gc_get_stack_begin();
#endif

  return;
}

#ifdef ATS_MULTITHREAD
gc_value gc_refresh_atomic_freelist(const unsigned int size_log)
{
  int i;
  gc_value temp;
  chunk_header* chunk_hdr;

  if (atomic_free_list_headers[size_log] != NULL) {
    atomic_free_list_headers[size_log]->on_free_list = 0;
    atomic_free_list_headers[size_log] = NULL;
  }

  pthread_mutex_lock(&atomic_sweep_lists_lock[size_log]);

  if (atomic_sweep_lists[size_log] == NULL) {
    pthread_mutex_unlock(&atomic_sweep_lists_lock[size_log]);
    pthread_mutex_lock(&free_list_lock);
    pthread_mutex_lock(&atomic_sweep_lists_lock[size_log]);

    if (atomic_sweep_lists[size_log] == NULL) {
      if (chunk_count == chunk_limit) {
        pthread_mutex_lock(&persistant_list_lock);
        pthread_mutex_lock(&global_root_list_lock);
	pthread_mutex_lock(&descriptors_mutex);

        for (i = 0; i < NUM_SIZE_BINS; i++) {
          if ((unsigned int)i != size_log)
            pthread_mutex_lock(&atomic_sweep_lists_lock[i]);
        }
        for (i = 0; i < NUM_SIZE_BINS; i++)
          pthread_mutex_lock(&sweep_lists_lock[i]);

        gc_collect();
        if (chunk_count == chunk_limit)
          chunk_limit *= 2;

        for (i = NUM_SIZE_BINS-1; i >= 0; i--)
          pthread_mutex_unlock(&sweep_lists_lock[i]);
        for (i = NUM_SIZE_BINS-1; i >= 0; i--) {
          if ((unsigned int)i != size_log)
            pthread_mutex_unlock(&atomic_sweep_lists_lock[i]);
        }

	pthread_mutex_unlock(&descriptors_mutex);
        pthread_mutex_unlock(&global_root_list_lock);
        pthread_mutex_unlock(&persistant_list_lock);
      }
      if (atomic_sweep_lists[size_log] == NULL) {
        chunk_count++;
        temp = gc_create_chunk(1, size_log, 1 << size_log);
        pthread_mutex_unlock(&atomic_sweep_lists_lock[size_log]);
        pthread_mutex_unlock(&free_list_lock);
	return temp;
      }
    }
    pthread_mutex_unlock(&free_list_lock);
  }

  chunk_hdr = atomic_sweep_lists[size_log];
  atomic_sweep_lists[size_log] = chunk_hdr->sweep_next;
  temp = (chunk_hdr->chunk_ptr + gc_thread_chunk(chunk_hdr->chunk_ptr, size_log, chunk_hdr->mark_bits));
  atomic_free_list_headers[size_log] = chunk_hdr;
  chunk_hdr->on_free_list = 1;
  pthread_mutex_unlock(&atomic_sweep_lists_lock[size_log]);
  return temp;
}
#else
gc_value gc_refresh_atomic_freelist(const unsigned int size_log)
{
  chunk_header* chunk_hdr;

  if (atomic_sweep_lists[size_log] == NULL) {
    if (chunk_count == chunk_limit) {
      gc_collect();
      if (chunk_count == chunk_limit)
        chunk_limit *= 2;
    }
    if (atomic_sweep_lists[size_log] == NULL) {
      chunk_count++;
      return gc_create_chunk(1, size_log, 1 << size_log);
    }
  }

  chunk_hdr = atomic_sweep_lists[size_log];
  atomic_sweep_lists[size_log] = chunk_hdr->sweep_next;
  return (chunk_hdr->chunk_ptr + gc_thread_chunk(chunk_hdr->chunk_ptr, size_log, chunk_hdr->mark_bits));
}
#endif

#ifdef ATS_MULTITHREAD
gc_value gc_refresh_freelist(const unsigned int size_log)
{
  int i;
  gc_value temp;
  chunk_header* chunk_hdr;

  if (free_list_headers[size_log] != NULL) {
    free_list_headers[size_log]->on_free_list = 0;
    free_list_headers[size_log] = NULL;
  }

  pthread_mutex_lock(&sweep_lists_lock[size_log]);

  if (sweep_lists[size_log] == NULL) {
    pthread_mutex_unlock(&sweep_lists_lock[size_log]);
    pthread_mutex_lock(&free_list_lock);
    pthread_mutex_lock(&sweep_lists_lock[size_log]);

    if (sweep_lists[size_log] == NULL) {
      if (chunk_count == chunk_limit) {
        pthread_mutex_lock(&persistant_list_lock);
        pthread_mutex_lock(&global_root_list_lock);
	pthread_mutex_lock(&descriptors_mutex);

        for (i = 0; i < NUM_SIZE_BINS; i++)
	  pthread_mutex_lock(&atomic_sweep_lists_lock[i]);

	for (i = 0; i < NUM_SIZE_BINS; i++) {
	  if ((unsigned int)i != size_log)
	    pthread_mutex_lock(&sweep_lists_lock[i]);
	}

        gc_collect();
        if (chunk_count == chunk_limit)
          chunk_limit *= 2;

        for (i = NUM_SIZE_BINS-1; i >= 0; i--) {
	  if ((unsigned int)i != size_log)
	    pthread_mutex_unlock(&sweep_lists_lock[i]);
	}
        for (i = NUM_SIZE_BINS-1; i >= 0; i--)
	  pthread_mutex_unlock(&atomic_sweep_lists_lock[i]);

	pthread_mutex_unlock(&descriptors_mutex);
        pthread_mutex_unlock(&global_root_list_lock);
        pthread_mutex_unlock(&persistant_list_lock);
      }
      if (sweep_lists[size_log] == NULL) {
        chunk_count++;
        temp = gc_create_chunk(0, size_log, 1 << size_log);
        pthread_mutex_unlock(&sweep_lists_lock[size_log]);
        pthread_mutex_unlock(&free_list_lock);
        return temp;
      }
    }
    pthread_mutex_unlock(&free_list_lock);
  }

  chunk_hdr = sweep_lists[size_log];
  sweep_lists[size_log] = chunk_hdr->sweep_next;
  temp = (chunk_hdr->chunk_ptr + gc_thread_chunk(chunk_hdr->chunk_ptr, size_log, chunk_hdr->mark_bits));
  chunk_hdr->on_free_list = 1;
  free_list_headers[size_log] = chunk_hdr;
  pthread_mutex_unlock(&sweep_lists_lock[size_log]);
  return temp;
}
#else
gc_value gc_refresh_freelist(const unsigned int size_log)
{
  chunk_header* chunk_hdr;

  if (sweep_lists[size_log] == NULL) {
    if (chunk_count == chunk_limit) {
      gc_collect();
      if (chunk_count == chunk_limit)
	chunk_limit *= 2;
    }
    if (sweep_lists[size_log] == NULL) {
      chunk_count++;
      return gc_create_chunk(0, size_log, 1 << size_log);
    }
  }

  chunk_hdr = sweep_lists[size_log];
  sweep_lists[size_log] = chunk_hdr->sweep_next;
  return (chunk_hdr->chunk_ptr + gc_thread_chunk(chunk_hdr->chunk_ptr, size_log, chunk_hdr->mark_bits));
}
#endif

#ifdef ATS_MULTITHREAD
gc_value gc_big_alloc_word
  (const size_t size, const unsigned int is_atomic)
{
  unsigned int num_chunks;
  gc_value temp;
  int i;

  num_chunks = (size + CHUNK_WORD_SIZE - 1) / CHUNK_WORD_SIZE;

  pthread_mutex_lock(&free_list_lock);

  if (chunk_count + num_chunks > chunk_limit) {
    pthread_mutex_lock(&persistant_list_lock);
    pthread_mutex_lock(&global_root_list_lock);
    pthread_mutex_lock(&descriptors_mutex);

    for (i = 0; i < NUM_SIZE_BINS; i++)
      pthread_mutex_lock(&atomic_sweep_lists_lock[i]);
    for (i = 0; i < NUM_SIZE_BINS; i++)
      pthread_mutex_lock(&sweep_lists_lock[i]);

    gc_collect();
    while (chunk_count + num_chunks > chunk_limit)
      chunk_limit *= 2;

    for (i = NUM_SIZE_BINS-1; i >= 0; i--)
      pthread_mutex_unlock(&sweep_lists_lock[i]);
    for (i = NUM_SIZE_BINS-1; i >= 0; i--)
      pthread_mutex_unlock(&atomic_sweep_lists_lock[i]);

    pthread_mutex_unlock(&descriptors_mutex);
    pthread_mutex_unlock(&global_root_list_lock);
    pthread_mutex_unlock(&persistant_list_lock);
  }
  temp = gc_create_chunk(is_atomic, LARGEST_BLOCK_SIZE_IN_CHUNK_LOG, size);
  chunk_count += num_chunks;
  pthread_mutex_unlock(&free_list_lock);
  return temp;
}
#else
gc_value gc_big_alloc_word
  (const size_t size, const unsigned int is_atomic)
{
  unsigned int num_chunks;
  gc_value temp;

  num_chunks = (size + CHUNK_WORD_SIZE - 1) / CHUNK_WORD_SIZE;
  if (chunk_count + num_chunks > chunk_limit) {
    gc_collect();
    while (chunk_count + num_chunks > chunk_limit)
      chunk_limit *= 2;
  }
  temp = gc_create_chunk(is_atomic, LARGEST_BLOCK_SIZE_IN_CHUNK_LOG, size);
  chunk_count += num_chunks;
  return temp;
}
#endif

/* ****** ****** */

// The following code is added by Hongwei Xi (June 2007)

static chunk_header* gc_ptr_chunk(const gc_value ptr)
{
  uintptr_t top_offset, bottom_offset;
  bottom_level_table* bottom_level;

  SPLIT_PTR_NO_CHUNK((uintptr_t)ptr, top_offset, bottom_offset);

#if (__WORDSIZE == 32)
  bottom_level = top_level[top_offset];
#elif (__WORDSIZE == 64)
  bottom_level = top_level[top_offset % TOP_LEVEL_HASH_SIZE];
  while (bottom_level != NULL && bottom_level->key != top_offset)
    bottom_level = bottom_level->hash_next;
#endif

  if (bottom_level == NULL) return NULL;
  return bottom_level->chunk_headers[bottom_offset];
}


/*
 * Hongwei Xi:
 *
 * I am not sure whether the following two functions are thread-safe
 * or not. It is difficult to do any effective formal reasoning given
 * the rather complicated implementation.
 *
 */

void gc_free (gc_value ptr) {
  chunk_header* chunk_hdr;
  chunk_hdr = gc_ptr_chunk(ptr);
  if (!chunk_hdr) {
    fprintf(stderr, "GC FATAL ERROR! pointer <%p> is lost\n", ptr);
    exit(1);
  }

  /*
  fprintf(stdout, "gc_free: size_log = %i\n", chunk_hdr->element_size_log);
  */

  if (chunk_hdr->element_size >= LARGEST_BLOCK_SIZE_IN_CHUNK) {
    gc_destroy_chunk(chunk_hdr);
  } else {
    *((gc_value *)ptr) = free_lists[chunk_hdr->element_size_log];
    free_lists[chunk_hdr->element_size_log] = ptr;
  }

  return;
}

gc_value gc_realloc_word(gc_value ptr, const size_t size)
{
  chunk_header* chunk_hdr;
  chunk_hdr = gc_ptr_chunk(ptr);
  gc_value ptr_new;

  if (!chunk_hdr) {
    fprintf(stderr, "GC FATAL ERROR! pointer <%p> is lost\n", ptr);
    exit(1);
  }

  if (chunk_hdr->element_size >= size) return ptr;

  if (chunk_hdr->element_size > LARGEST_BLOCK_SIZE_IN_CHUNK) {
    gc_destroy_chunk(chunk_hdr);
  } else {
    *((gc_value *)ptr) = free_lists[chunk_hdr->element_size_log];
    free_lists[chunk_hdr->element_size_log] = ptr;
  }

  ptr_new = gc_alloc_word(size);
  memcpy(ptr_new, ptr, chunk_hdr->element_size << BYTES_PER_WORD);
  return ptr_new;
}
