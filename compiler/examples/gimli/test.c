#include <stdint.h>
#include <stdio.h>

extern void gimli(uint32_t *);

int main()
{
  uint32_t x[12];
  int i;

  for (i = 0;i < 12;++i) x[i] = i * i * i + i * 0x9e3779b9;

  for (i = 0;i < 12;++i) {
    printf("%08x ",x[i]);
    if (i % 4 == 3) printf("\n");
  }
  printf("----------------------\n");

  gimli(x);

  for (i = 0;i < 12;++i) {
    printf("%08x ",x[i]);
    if (i % 4 == 3) printf("\n");
  }
  printf("----------------------\n");
  return 0;
}
