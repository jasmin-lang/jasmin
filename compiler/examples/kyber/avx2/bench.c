#include "params.h"
#include "reduce.h"
#include "ntt.h"

#ifndef BENCH_WARM
#define BENCH_WARM 100
#endif

#ifndef BENCH_LOOPS
#define BENCH_LOOPS 1
#endif

#ifndef BENCH_CYCLES
#define BENCH_CYCLES 100000
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

#define KYBER_N 256
#define KYBER_Q 7681

const uint64_t zetas_mil[KYBER_N] = {
  990, 7427, 2634, 6819, 578, 3281, 2143, 1095, 484, 6362, 3336, 5382, 6086, 3823, 877, 5656,
  3583, 7010, 6414, 263, 1285, 291, 7143, 7338, 1581, 5134, 5184, 5932, 4042, 5775, 2468, 3,
  606, 729, 5383, 962, 3240, 7548, 5129, 7653, 5929, 4965, 2461, 641, 1584, 2666, 1142, 157,
  7407, 5222, 5602, 5142, 6140, 5485, 4931, 1559, 2085, 5284, 2056, 3538, 7269, 3535, 7190, 1957,
  3465, 6792, 1538, 4664, 2023, 7643, 3660, 7673, 1694, 6905, 3995, 3475, 5939, 1859, 6910, 4434,
  1019, 1492, 7087, 4761, 657, 4859, 5798, 2640, 1693, 2607, 2782, 5400, 6466, 1010, 957, 3851,
  2121, 6392, 7319, 3367, 3659, 3375, 6430, 7583, 1549, 5856, 4773, 6084, 5544, 1650, 3997, 4390,
  6722, 2915, 4245, 2635, 6128, 7676, 5737, 1616, 3457, 3132, 7196, 4702, 6239, 851, 2122, 3009,
  7613, 7295, 2007, 323, 5112, 3716, 2289, 6442, 6965, 2713, 7126, 3401, 963, 6596, 607, 5027,
  7078, 4484, 5937, 944, 2860, 2680, 5049, 1777, 5850, 3387, 6487, 6777, 4812, 4724, 7077, 186,
  6848, 6793, 3463, 5877, 1174, 7116, 3077, 5945, 6591, 590, 6643, 1337, 6036, 3991, 1675, 2053,
  6055, 1162, 1679, 3883, 4311, 2106, 6163, 4486, 6374, 5006, 4576, 4288, 5180, 4102, 282, 6119,
  7443, 6330, 3184, 4971, 2530, 5325, 4171, 7185, 5175, 5655, 1898, 382, 7211, 43, 5965, 6073,
  1730, 332, 1577, 3304, 2329, 1699, 6150, 2379, 5113, 333, 3502, 4517, 1480, 1172, 5567, 651,
  925, 4573, 599, 1367, 4109, 1863, 6929, 1605, 3866, 2065, 4048, 839, 5764, 2447, 2022, 3345,
  1990, 4067, 2036, 2069, 3567, 7371, 2368, 339, 6947, 2159, 654, 7327, 2768, 6676, 987, 2214};

extern void ntt_mil(uint64_t *p, const uint64_t *zetas);

uint16_t a[256] __attribute__((aligned(32)));
uint64_t b[256];

int main()
{
  int trash;

  FILE* urandom;

  /* Initialize a and b with random coefficients */
  urandom = fopen("/dev/urandom", "r");
  trash=fread(a, 2, KYBER_N, urandom);
  for(int i=0;i<KYBER_N;i++)
  {
    a[i] %= KYBER_Q;
    b[i] = a[i];
  }
  fclose(urandom);

  
  uint64_t __c__, __l__, __start__, __end__;
  bench *__b__;
  bench_init(&__b__, BENCH_CYCLES);
  for(__c__=0; __c__<BENCH_WARM; __c__++)
  { ntt_mil(b,zetas_mil); }

  bench_print_header(stdout);
  for(__l__=0; __l__<BENCH_LOOPS; __l__++)
  { bench_reset(__b__);
    for(__c__=0; __c__<BENCH_CYCLES; __c__++)
    { __start__ = bench_get_time();
      ntt_mil(b,zetas_mil);
      __end__ = bench_get_time();
      bench_add(__b__,__start__,__end__);
    }
    bench_set_median(__b__);
    bench_print(__b__,stdout,__l__);
  }

  bench_init(&__b__, BENCH_CYCLES);
  for(__c__=0; __c__<BENCH_WARM; __c__++)
  { ntt(a,zetas_exp); }

  bench_print_header(stdout);
  for(__l__=0; __l__<BENCH_LOOPS; __l__++)
  { bench_reset(__b__);
    for(__c__=0; __c__<BENCH_CYCLES; __c__++)
    { __start__ = bench_get_time();
      ntt(a,zetas_exp);
      __end__ = bench_get_time();
      bench_add(__b__,__start__,__end__);
    }
    bench_set_median(__b__);
    bench_print(__b__,stdout,__l__);
  }

  return 0;
}


