#include <stdint.h>

extern
void swap4 (uint64_t x[4], uint64_t y[4], uint64_t swap, uint64_t sb);

#include <stdio.h>

int
main(void)
{
	uint64_t str[8] = { 1, 2, 3, 4, 5, 6, 7, 8 };

	uint64_t s;

	if (scanf("%llu", &s) != 1) return -1;

	swap4(str, str + 4, s & 1, 0);

	for (unsigned i = 0; i < 8; ++i) {
		printf("%llu%s", str[i], i == 7 ? ".\n" : " ");
	}

	return 0;
}
