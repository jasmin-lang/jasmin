#include "stdio.h"

typedef unsigned long int u64;

extern void scalarmult(u64[], u64[], u64[]);
//extern test_ladderstep(u64[], u64[], u64[],u64[], u64[], u64[]);
//extern void test_mladder(u64[], u64[], u64[]);
int main() {
        
        u64 b[4] = { 9, 0, 0, 0};
        u64 e[4] = {0x7da518730a6d0777,0x4566b25172c1163c,
        	        0x2a99c0eb872f4cdf,0x2a2cb91da5fb77b1};
        u64 r[4];
        scalarmult(r,e,b);
        printf("0x%016lx%016lx%016lx%016lx\n",r[3],r[2],r[1],r[0]);

        /*
		u64 one[4] = { 1, 0, 0, 0};
        u64 e[4] = {0x7da518730a6d0777,0x4566b25172c1163c,
        	        0x2a99c0eb872f4cdf,0x2a2cb91da5fb77b1};
        u64 r[4*4];
        test_ladderstep(e,e,one,e,one,r);
        printf("%lx %lx %lx %lx\n",r[3],r[2],r[1],r[0]);
        printf("%lx %lx %lx %lx\n",r[7],r[6],r[5],r[4]);
        printf("%lx %lx %lx %lx\n",r[11],r[10],r[9],r[8]);
        printf("%lx %lx %lx %lx\n",r[15],r[14],r[13],r[12]);

        u64 b[4] = { 9, 0, 0, 0};
        u64 e[4] = {0x7da518730a6d0777,0x4566b25172c1163c,
        	          0x2a99c0eb872f4cdf,0x2a2cb91da5fb77b1};
        //u64 e[4] = { 6, 0, 0, 0};
        u64 r[2*4];
        test_mladder(r,e,b);
        printf("0x%lx%lx%lx%lx\n",r[3],r[2],r[1],r[0]);
        printf("0x%lx%lx%lx%lx\n",r[7],r[6],r[5],r[4]);*/
} 

// 2a2cb91da5fb77b12a99c0eb872f4cdf4566b25172c1163c7da518730a6d0777