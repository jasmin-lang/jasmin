#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

typedef uint64_t u64;

#define MAX_U64 0xffffffffffffffff

/* Addition with carry
 *********************************************************************/

void add_carry(u64 *cf_out, u64 *z_out, u64 x_in, u64 y_in, u64 cf_in) {
  u64 cf_temp = 0;
  if (cf_in == 0) {
    asm volatile (
      "addq %[y], %[x];"
      "adcq $0, %[cf];"  // read cf register
      :   [x]  "+r" (x_in)
        , [cf] "+r" (cf_temp)
      :   [y]  "r"  (y_in)
    );
  } else {
    asm volatile (
      "stc;" // set carry flag
      "adcq %[y], %[x];"
      "adcq $0, %[cf];"   // read cf register
      :   [x]  "+r" (x_in)
        , [cf] "+r" (cf_temp)
      :   [y]  "r"  (y_in)
    );
  }
  *z_out = x_in;
  *cf_out = cf_temp;
}


/* Subtraction with carry
 *********************************************************************/

void sub_carry(u64 *cf_out, u64 *z_out, u64 x_in, u64 y_in, u64 cf_in) {
  u64 cf_temp = 0;
  if (cf_in == 0) {
    asm volatile (
      "subq %[y], %[x];"
      "adcq $0, %[cf];"  // read cf register
      :   [x]  "+r" (x_in)
        , [cf] "+r" (cf_temp)
      :   [y]  "r"  (y_in)
    );
  } else {
    asm volatile (
      "stc;" // set carry flag
      "sbbq %[y], %[x];"
      "adcq $0, %[cf];"   // read cf register
      :   [x]  "+r" (x_in)
        , [cf] "+r" (cf_temp)
      :   [y]  "r"  (y_in)
    );
  }
  *z_out = x_in;
  *cf_out = cf_temp;
}

/* Unsigned multiplication: u64 x u64 -> u128
 *********************************************************************/

void mul_128(u64 *h_out, u64 *l_out, u64 x_in, u64 y_in) {
  u64 h_temp, l_temp;
  asm volatile (
    "movq %[x], %%rax;"
    "mulq %[y];"
    "movq %%rax, %[l];"
    "movq %%rdx, %[h];"
    :   [h] "=r" (h_temp)
      , [l] "=r" (l_temp)
    :   [x] "r"  (x_in)
      , [y] "r"  (y_in)
  );
  *h_out = h_temp;
  *l_out = l_temp;
}

/* signed multiplication with truncation: u64 x u64 -> u64
 *********************************************************************/

void imul_trunc(u64 *cf_out, u64 *l_out, u64 x_in, u64 y_in) {
  u64 cf_temp = 0;
  asm volatile (
    "imulq %[y], %[x];"
    "adcq $0, %[cf];"  // read cf register
    :   [x]  "+r" (x_in)
      , [cf] "+r" (cf_temp)
    :   [y]  "r"  (y_in)
    : "%rdx", "%rax"
  );
  *l_out  = x_in;
  *cf_out = cf_temp;
}

#ifdef TEST

/* Tests
 *********************************************************************/

void test_add_carry() {
  u64 x  = MAX_U64 - 2;
  u64 y  = 1;
  u64 z  = 0;
  u64 cf = 0;

  add_carry(&cf, &z, MAX_U64 - 1 , 1, 0);
  assert(z == MAX_U64 && cf == 0);

  add_carry(&cf, &z, MAX_U64 - 1 , 1, 1);
  assert(z == 0 && cf == 1);

  add_carry(&cf, &z, 1, 1, 0);
  assert(z == 2 && cf == 0);

  add_carry(&cf, &z, 1, 1, 1);
  assert(z == 3 && cf == 0);

  // for printing
  // printf("x = %jx\ncf = %jx\n", z, cf);
}

void test_sub_carry() {
  u64 x, y, z, cf;

  // 1 - 1 = 0
  sub_carry(&cf, &z, 1 , 1, 0);
  assert(z == 0 && cf == 0);

  // 0 - 1 = unsigned(-1) = MAX_U64 with cf=1
  sub_carry(&cf, &z, 0, 1, 0);
  assert(z == MAX_U64 && cf == 1);

  // 1 - (1 + 1) = unsigned(-1) = MAX_U64 with cf=1
  sub_carry(&cf, &z, 1, 1, 1);
  assert(z == MAX_U64 && cf == 1);

  // 0 - MAX_U64 = unsigned(-MAX_u64) = 1 with cf=1  
  sub_carry(&cf, &z, 0, MAX_U64, 0);
  assert(z == 1 && cf == 1);

  // MAX_U64 - MAX_U64 = 0 with cf = 0  
  sub_carry(&cf, &z, MAX_U64, MAX_U64, 0);
  assert(z == 0 && cf == 0);
  
  // MAX_U64 - (MAX_U64 + 1) = MAX_U64 - 0 = MAX_U64 with cf=0
  sub_carry(&cf, &z, MAX_U64, MAX_U64, 1);
  assert(z == MAX_U64 && cf == 1);

  // 1 - MAX_U64 = 2 with cf = 1
  sub_carry(&cf, &z, 1, MAX_U64, 0);
  assert(z == 2 && cf == 1);

  // 1 - (MAX_U64 + 1) = 1 with cf = 1
  sub_carry(&cf, &z, 1, MAX_U64, 1);
  assert(z == 1 && cf == 1);

  // 1 - (MAX_U64 + 1) = 1 with cf = 1
  sub_carry(&cf, &z, 1, MAX_U64, 1);
  assert(z == 1 && cf == 1);

  // MAX_U64 - 1 with cf = 0
  sub_carry(&cf, &z, MAX_U64, 1, 0);
  assert(z == MAX_U64 - 1 && cf == 0);
  
  // MAX_U64 - (1 + 1) = MAX_U64 - 2 with cf = 0
  sub_carry(&cf, &z, MAX_U64, 1, 1);
  assert(z == MAX_U64 - 2 && cf == 0);
 
  // (MAX_U64 - 1) - MAX_U64 =  with cf = 1
  sub_carry(&cf, &z, MAX_U64 - 1, MAX_U64, 0);
  assert(z == MAX_U64 && cf == 1);
    
  // (MAX_U64 - 1) - (MAX_U64 + 1) =  with cf = 1
  sub_carry(&cf, &z, MAX_U64 - 1, MAX_U64, 1);
  assert(z == MAX_U64 - 1 && cf == 1);
}

void test_mul_128() {
  u64 x, y, h, l;

  // 0*0 = 0
  mul_128(&h, &l, 0 , 0);
  assert(h == 0 && l == 0);

  // 1*0 = 0
  mul_128(&h, &l, 1 , 0);
  assert(h == 0 && l == 0);

  // 1*1 = 1
  mul_128(&h, &l, 0 , 0);
  assert(h == 0 && l == 0);

  // 2*2 = 4
  mul_128(&h, &l, 2 , 2);
  assert(h == 0 && l == 4);

  // MAX_64*1 = 0|| MAX_64
  mul_128(&h, &l, MAX_U64 , 1);
  assert(h == 0 && l == MAX_U64);

  // MAX_64*MAX_64 = (MAX_64 - 1) || 0..01
  mul_128(&h, &l, MAX_U64 , MAX_U64);
  assert(h == MAX_U64 - 1 && l == 1);

  // MAX_64*2 = 0..01|| MAX_64 - 1
  mul_128(&h, &l, MAX_U64 , 2);
  assert(h == 1 && l == MAX_U64 - 1);
}

void test_imul_trunc() {
  u64 l, cf;

  // 0*38 = 0
  imul_trunc(&cf, &l, 0, 38);
  assert(l == 0 && cf == 0);

  // 1*38 = 38
  imul_trunc(&cf, &l, 1, 38);
  assert(l == 38 && cf == 0);

  // signed(MAX_U64)*38 = -1*38 = MAX_U64 - 37 (as unsigned)
  imul_trunc(&cf, &l, MAX_U64, 38);
  assert(l == 0xffffffffffffffda && cf == 0);

  // similar to previous
  imul_trunc(&cf, &l, MAX_U64 - 0xff00000000000000, 38);
  assert(l == 0x25ffffffffffffda && cf == 0);

  // signed(MAX_64)*signed(MAX_64) = -1 * -1 = 1
  imul_trunc(&cf, &l, MAX_U64 , MAX_U64);
  assert(l == 1 && cf == 0);

  // MAX_I64 * 2 = ... with cf = 1
  imul_trunc(&cf, &l, 0x7fffffffffffffff, 2);
  assert(l == 0xfffffffffffffffe && cf == 1);

  // MIN_I64 * 2 = 0 with cf = 1
  imul_trunc(&cf, &l, 0x8000000000000000, 2);
  assert(l == 0 && cf == 1);

  // (MIN_I64 + 1) * 2 = 0 with cf = 1
  imul_trunc(&cf, &l, 0x8000000000000001, 2);
  assert(l == 2 && cf == 1);
}

int main() {
  test_add_carry();
  test_sub_carry();
  test_mul_128();
  test_imul_trunc();
  printf("Tests finished successfully.\n");
  return 0;
}

#endif
