#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>

extern
void siphash_jazz(uint64_t*, size_t, uint64_t*, uint64_t*, size_t);
extern
int siphash(uint64_t*, size_t, uint64_t*, uint64_t*, size_t);

static inline
uint64_t bench_get_time(){
  unsigned int h, l;
  __asm__ __volatile__ ("rdtsc" : "=a" (l), "=d" (h));
  return ((uint64_t) h << 32) | l;
}

#define NBENCH 1024

static
uint64_t times[NBENCH] = {};

static
int
cmp(const void* x, const void* y) {
  uint64_t a = *(uint64_t*)x;
  uint64_t b = *(uint64_t*)y;
  if (a == b) return 0;
  if (a < b) return -1;
  return 1;
}

#define BENCH(f) \
  do {\
    for (int nbench = 0; nbench < NBENCH; ++nbench) {\
      uint64_t time = bench_get_time();\
      f;\
      times[nbench] = bench_get_time() - time;\
    }\
    qsort(times, NBENCH, sizeof(*times), cmp);\
  } while(0)

#define PRINTHASH(n)                            \
  for (int j = 0; j < n; ++j) {                 \
    printf("%02x", out[j]);                 \
  }                                             \
  printf("\t%"PRIu64"\t%"PRIu64"\t%"PRIu64"\n", times[NBENCH >> 2], times[NBENCH >> 1], times[(NBENCH >> 2) + (NBENCH >> 1)]);

int main(void)
{
  uint8_t in[64], out[16], k[16];
  int i;
  for (i = 0; i < 16; ++i)
    k[i] = i;

  for (int version = 0; version < 2; ++version) {
  for (i = 0; i < 64; ++i) {
    in[i] = i;
    size_t size = 8 * (1 + version);
    BENCH(siphash((void*)in, i, (void*)k, (void*)out, size));
    PRINTHASH(size);
    BENCH(siphash_jazz((void*)in, i, (void*)k, (void*)out, size));
    PRINTHASH(size);
    printf("\n");
  }
  }

  return 0;
}
