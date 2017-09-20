#ifndef BENCH_WARM
#define BENCH_WARM 20
#endif

#ifndef BENCH_LOOPS
#define BENCH_LOOPS 3
#endif

#ifndef BENCH_CYCLES
#define BENCH_CYCLES 1000
#endif

#ifndef BENCH_FVARS_DEC
#error define BENCH_FVARS_DEC - declare local vars
#endif 

#ifndef BENCH_FTYPE
#error define BENCH_FTYPE - function return type
#endif 

#ifndef BENCH_FNAME
#error define BENCH_FNAME - function name
#endif

#ifndef BENCH_FARGS_DEC
#error define BENCH_FARGS_DEC - function signature args
#endif

#ifndef BENCH_FVARS_CALL
#error define BENCH_FVARS_CALL - function args
#endif

#include <inttypes.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <time.h>
#include <assert.h>
#include <string.h>

typedef struct
{
  uint64_t *list;
  size_t size;
  size_t i;
  uint64_t p25;
  uint64_t median;
  uint64_t p75;
}bench;

inline uint64_t bench_get_time(){
  unsigned int h, l;
  __asm__ __volatile__ ("rdtsc" : "=a" (l), "=d" (h));
  return ((uint64_t) h << 32) | l;
}

static int bench_u64_cmp(const void *left, const void *right)
{
  if (*(const uint64_t *)left > *(const uint64_t *)right) return 1;
  if (*(const uint64_t *)left < *(const uint64_t *)right) return -1;
  return 0;
}

static int bench_init(bench **m, size_t n)
{
  assert(m);
  *m = (bench*) calloc(1, sizeof(bench));
  assert(*m);
  (*m)->list = (uint64_t*) calloc(n, sizeof(uint64_t));
  assert((*m)->list);
  (*m)->size = n;
  (*m)->i = 0;
  return 0;
}

static int bench_destroy(bench **m)
{
  assert(m && *m);
  free((*m)->list);
  free((*m));
  *m = NULL;
  return 0;
}

static int bench_add(bench *m, uint64_t start, uint64_t end)
{
  assert(m);
  if(m->i >= m->size)
    return -1;
  m->list[m->i] = (end - start);
  m->i++;
  return 0;
}

static int bench_set_median(bench *m)
{
  assert(m && m->list);
  qsort(m->list, m->i, sizeof(uint64_t), bench_u64_cmp);
  m->p25 = m->list[m->i >> 2];
  m->median = m->list[m->i >> 1];
  m->p75 = m->list[m->i - (m->i >> 2)];
  return 0;
}

static int bench_reset(bench *m)
{
  assert(m);
  memset(m->list, 0, sizeof(uint64_t) * m->size);
  m->i = 0;
  m->p25 = 0;
  m->median = 0;
  m->p75 = 0;
  return 0;
}

static int bench_print_header(FILE *f)
{
  fprintf(f, "run,percentil25,percentil75,median\n");
  fflush(f);
  return 0;
}

static int bench_print(bench *m, FILE *f, size_t n)
{
  fprintf(f, "%zu,%" PRIu64 ",%" PRIu64 ",%" PRIu64 "\n", n, m->p25, m->p75, m->median);
  fflush(f);
  return 0;
}

extern BENCH_FTYPE BENCH_FNAME(BENCH_FARGS_DEC);

int main()
{
  BENCH_FVARS_DEC
  
  uint64_t __c__, __l__, __start__, __end__;
  bench *__b__;
  bench_init(&__b__, BENCH_CYCLES);
  for(__c__=0; __c__<BENCH_WARM; __c__++)
  { BENCH_FNAME(BENCH_FVARS_CALL); }

  bench_print_header(stdout);
  for(__l__=0; __l__<BENCH_LOOPS; __l__++)
  { bench_reset(__b__);
    for(__c__=0; __c__<BENCH_CYCLES; __c__++)
    { __start__ = bench_get_time();
      BENCH_FNAME(BENCH_FVARS_CALL);
      __end__ = bench_get_time();
      bench_add(__b__,__start__,__end__);
    }
    bench_set_median(__b__);
    bench_print(__b__,stdout,__l__);
  }
  return 0;
}


