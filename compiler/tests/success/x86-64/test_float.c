#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>


extern double addsd(double x, double y);
extern double subsd(double x, double y);
extern double mulsd(double x, double y);
extern uint64_t cvttsd2si(double x);
extern uint64_t cvtsd2si(double x);
extern double cvtsi2sd(uint64_t x);
extern uint64_t cmpeqsd(double x, double y);
extern uint64_t cmpltsd(double x, double y);
extern uint64_t cmplesd(double x, double y);
extern uint64_t cmpunordsd(double x, double y);
extern uint64_t cmpneqsd(double x, double y);
extern uint64_t cmpnltsd(double x, double y);
extern uint64_t cmpnlesd(double x, double y);
extern uint64_t cmpordsd(double x, double y);


int main() {
 double a, b, c;
 uint64_t ci, di;

 a = 1.25;
 b = 2.25;

 c = addsd(a, b);
 printf("%lf + %lf = %lf\n", a, b, c);
 c = subsd(a, b);
 printf("%lf - %lf = %lf\n", a, b, c);
 c = mulsd(a, b);
 printf("%lf * %lf = %lf\n", a, b, c);
 ci = cvttsd2si(c);
 printf("floor(%lf) = %lld\n", c, ci);
 ci = cvtsd2si(c);
 printf("round(%lf) = %lld\n", c, ci);
 ci = cmpltsd(a, b);
 printf("%lf < %lf = %d\n", a, b, ci!=0);
 ci = cmpneqsd(a, a);
 printf("%lf != %lf = %d\n", a, a, ci!=0);
 di = 3345;
 c = cvtsi2sd(di);
 printf("double(%lld) = %lf\n", di, c);

 return 0;
}
