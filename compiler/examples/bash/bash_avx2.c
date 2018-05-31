/*
*******************************************************************************
\file bash_avx2.c
\brief STB 34.101.77 (bash): hashing algorithms, AVX implementation
\project bee2 [cryptographic library]
\author (C) Sergey Agievich [agievich@{bsu.by|gmail.com}]
\author (C) Vlad Semenov [semenov.vlad.by@gmail.com]
\created 2015.12.13
\version 2016.04.23
\license This program is released under the GNU General Public License
version 3. See Copyright Notices in bee2/info.h.
*******************************************************************************
*/

#include "bash_avx2.h"
#include <memory.h>
#include <string.h>
#define memCopy(dest, src, count) memcpy(dest, src, count)
#define memMove(dest, src, count) memmove(dest, src, count)
#define memSet(buf, c, count) memset(buf, c, count)
#define memSetZero(buf, count) memSet(buf, 0, count)
#define memEq(buf1, buf2, count) (memcmp(buf1, buf2, count) == 0)
#define ASSERT(x) 
#define u64RotHi(w, d)\
	((u64)((w) << d | (w) >> (64 - d)))
#define u64RotLo(w, d)\
	((u64)((w) >> d | (w) << (64 - d)))
#define u64Rev(w)\
	((u64)((w) << 56 | ((w) & 0xFF00) << 40 | ((w) & 0xFF0000) << 24 |\
	((w) & 0xFF000000) << 8 | ((w) >> 8 & 0xFF000000) |\
	((w) >> 24 & 0xFF0000) | ((w) >> 40 & 0xFF00) | (w) >> 56))
void u64Rev2(u64 buf[], size_t count)
{
	while (count--)
		buf[count] = u64Rev(buf[count]);
}


#if defined(__AVX2__)
#include <immintrin.h>

typedef __m256i u256;

#define LOADW(s) _mm256_loadu_si256( (__m256i const *)(s) )
#define STOREW(s,w) _mm256_storeu_si256( (__m256i *)(s), (w) )

#if defined(_MSC_VER)
#define I(W,n) W.m256i_u64[n]
#else
#define I(W,n) W[n]
#endif

#define S4(w0,w1,w2,w3) _mm256_set_epi64x(w3,w2,w1,w0)
#define X4(w1,w2) _mm256_xor_si256(w1,w2)
#define O4(w1,w2) _mm256_or_si256(w1,w2)
#define A4(w1,w2) _mm256_and_si256(w1,w2)
#define AN4(w1,w2) _mm256_andnot_si256(w1,w2) /* (~w1) & w2 */
#define NA4(w1,w2) AN4(w2,w1)

#define ROLV(a, i0, i1, i2, i3) \
	X4(_mm256_sllv_epi64(a, S4(i0, i1, i2, i3)), \
		_mm256_srlv_epi64(a, S4(64-i0, 64-i1, 64-i2, 64-i3)))

#define PERM4X64(w,i) _mm256_permute4x64_epi64(w,i)
#define PERM2X128(w0,w1,i) _mm256_permute2x128_si256(w0,w1,i)

#define R4(m0,m1,m2,m3, W) ROLV(W, m0,m1,m2,m3)

#else
#error "The compiler does not support AVX2 intrinsics."
#endif


/* S0,S1,S2,S3 S4,S5,S6,S7 -> S1,S0,S3,S2 S5,S4,S7,S6
    w0=S0,S1,S2,S3 w1=S4,S5,S6,S7
 -> s0=S1,S0,S3,S2 s1=S5,S4,S7,S6
*/
#define PP01(W0,W1, S0,S1) \
    do { \
        S0 = PERM4X64( W0, 0xb1 ); \
        S1 = PERM4X64( W1, 0xb1 ); \
    } while (0)

/* S16,S17,S18,S19 S20,S21,S22,S23 -> S22,S19,S16,S21 S18,S23,S20,S17
    w4=S16,S17,S18,S19 w5=S20,S21,S22,S23
 -> u4=S16,S19,S18,S17 u5=S20,S23,S22,S21
 -> t4=S16,S19,S22,S21 t5=S20,S23,S18,S17
 -> s4=S22,S19,S16,S21 s5=S18,S23,S20,S17
*/
#define PP45_1(W4,W5, U4,U5,T4,T5) \
    do { \
        U4 = PERM4X64( W4, 0x6c ); \
        U5 = PERM4X64( W5, 0x6c ); \
        T4 = PERM2X128( U4, U5, 0x30 ); \
        T5 = PERM2X128( U4, U5, 0x12 ); \
    } while (0)
#define PP45_2(T4,T5, S4,S5) \
    do { \
        S4 = PERM4X64( T4, 0xc6 ); \
        S5 = PERM4X64( T5, 0xc6 ); \
    } while (0)

#define bashPP(W0,W1,W2,W3,W4,W5 ,Y0,Y1,Y2,Y3,Y4,Y5 ,T4,T5 ,U4,U5) \
    do { \
        PP45_1(W4,W5, U4,U5,T4,T5); \
        PP01(W0,W1, Y4,Y5); \
        Y0=W2; Y1=W3; \
        PP45_2(T4,T5, Y2,Y3); \
    } while(0)

#define bashP0(W0,W1,W2,W3,W4,W5 ,T4,T5 ,U4,U5) \
    bashPP(W0,W1,W2,W3,W4,W5 ,W0,W1,W2,W3,W4,W5 ,T4,T5 ,U4,U5)

#define bashP1(W0,W1,W2,W3,W4,W5 ,T4,T5 ,U4,U5) \
    bashPP(W0,W1,W2,W3,W4,W5 ,W0,W1,W3,W2,W5,W4 ,T4,T5 ,U4,U5)


#define bashSP(SS, m10,m11,m12,m13, n10,n11,n12,n13, m20,m21,m22,m23, n20,n21,n22,n23, W0,W1,W2 ,S1,S2,T0,T1,T2,U0,U1,U2) \
    do { \
        S2 = R4(m10,m11,m12,m13, W0); \
        U0 = X4(W0, X4(W1, W2)); \
        S1 = X4(W1, R4(n10,n11,n12,n13, U0)); \
        U2 = X4(X4(W2, R4(m20,m21,m22,m23, W2)), R4(n20,n21,n22,n23, S1)); \
        U1 = X4(S1, S2); \
        SS(U0,U1,U2, T0,T1,T2); \
        W1 = X4(U1, T1); \
        W2 = X4(U2, T2); \
        W0 = X4(U0, T0);; \
    } while (0)

#define bashSS0(U0,U1,U2, T0,T1,T2) \
    do { \
        T1 = O4(U0, U2); \
        T2 = A4(U0, U1); \
        T0 = NA4(U2, U1);; \
    } while (0)

#define bashSS1(U0,U1,U2, T0,T1,T2) \
    do { \
        T1 = A4(U0, U2);; \
        T2 = O4(U0, U1);; \
        T0 = AN4(U2, U1);; \
    } while (0)

#define bashS0(m10,m11,m12,m13, n10,n11,n12,n13, m20,m21,m22,m23, n20,n21,n22,n23, W0,W1,W2 ,S1,S2,T0,T1,T2,U0,U1,U2) \
    bashSP(bashSS0, m10,m11,m12,m13, n10,n11,n12,n13, m20,m21,m22,m23, n20,n21,n22,n23, W0,W1,W2 ,S1,S2,T0,T1,T2,U0,U1,U2)

#define bashS1(m10,m11,m12,m13, n10,n11,n12,n13, m20,m21,m22,m23, n20,n21,n22,n23, W0,W1,W2 ,S1,S2,T0,T1,T2,U0,U1,U2) \
    bashSP(bashSS1, m10,m11,m12,m13, n10,n11,n12,n13, m20,m21,m22,m23, n20,n21,n22,n23, W0,W1,W2 ,S1,S2,T0,T1,T2,U0,U1,U2)


#define f(x) ((x*7) % 64)
#define m1 8
#define n1 53
#define m2 14
#define n2 1

#define m10 m1
#define m11 f(m10)
#define m12 f(m11)
#define m13 f(m12)
#define m14 f(m13)
#define m15 f(m14)
#define m16 f(m15)
#define m17 f(m16)

#define n10 n1
#define n11 f(n10)
#define n12 f(n11)
#define n13 f(n12)
#define n14 f(n13)
#define n15 f(n14)
#define n16 f(n15)
#define n17 f(n16)

#define m20 m2
#define m21 f(m20)
#define m22 f(m21)
#define m23 f(m22)
#define m24 f(m23)
#define m25 f(m24)
#define m26 f(m25)
#define m27 f(m26)

#define n20 n2
#define n21 f(n20)
#define n22 f(n21)
#define n23 f(n22)
#define n24 f(n23)
#define n25 f(n24)
#define n26 f(n25)
#define n27 f(n26)


#define bashR0(W0,W1,W2,W3,W4,W5,C ,S1,S2,T0,T1,T2,U0,U1,U2) \
    do { \
        bashS0(m10,m11,m12,m13, n10,n11,n12,n13, m20,m21,m22,m23, n20,n21,n22,n23, W0,W2,W4 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashS0(m14,m15,m16,m17, n14,n15,n16,n17, m24,m25,m26,m27, n24,n25,n26,n27, W1,W3,W5 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashP0(W0,W1,W2,W3,W4,W5 ,T0,T1,U0,U1); \
        I( W4, 0 ) ^= C; \
    } while (0)

#define bashR1(W0,W1,W2,W3,W4,W5,C ,S1,S2,T0,T1,T2,U0,U1,U2) \
    do { \
        bashS1(m17,m12,m11,m14, n17,n12,n11,n14, m27,m22,m21,m24, n27,n22,n21,n24, W0,W2,W4 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashS1(m13,m16,m15,m10, n13,n16,n15,n10, m23,m26,m25,m20, n23,n26,n25,n20, W1,W3,W5 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashP1(W0,W1,W2,W3,W4,W5 ,T0,T1,U0,U1); \
        I( W5, 3 ) ^= C; \
    } while (0)


#define CX 0xDC2BE1997FE0D8AEull
#define FC(C) (((C) & 1) ? (((C) >> 1) ^ (CX)): ((C) >> 1))
#define C0 0x3bf5080ac8ba94b1ull
#define C1 0xc1d1659c1bbd92f6ull
#define C2 0x60e8b2ce0ddec97bull
#define C3 0xec5fb8fe790fbc13ull
#define C4 0xaa043de6436706a7ull
#define C5 0x8929ff6a5e535bfdull
#define C6 0x98bf1e2c50c97550ull
#define C7 0x4c5f8f162864baa8ull
#define C8 0x262fc78b14325d54ull
#define C9 0x1317e3c58a192eaaull
#define C10 0x98bf1e2c50c9755ull
#define C11 0xd8ee19681d669304ull
#define C12 0x6c770cb40eb34982ull
#define C13 0x363b865a0759a4c1ull
#define C14 0xc73622b47c4c0aceull
#define C15 0x639b115a3e260567ull
#define C16 0xede6693460f3da1dull
#define C17 0xaad8d5034f9935a0ull
#define C18 0x556c6a81a7cc9ad0ull
#define C19 0x2ab63540d3e64d68ull
#define C20 0x155b1aa069f326b4ull
#define C21 0xaad8d5034f9935aull
#define C22 0x556c6a81a7cc9adull
#define C23 0xde8082cd72debc78ull


#define bashFP(W0,W1,W2,W3,W4,W5 ,S1,S2,T0,T1,T2,U0,U1,U2) \
    do { \
        bashR0(W0,W1,W2,W3,W4,W5,C0 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C1 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C2 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C3 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C4 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C5 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C6 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C7 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C8 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C9 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C10 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C11 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C12 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C13 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C14 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C15 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C16 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C17 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C18 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C19 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C20 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C21 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR0(W0,W1,W2,W3,W4,W5,C22 ,S1,S2,T0,T1,T2,U0,U1,U2); \
        bashR1(W0,W1,W2,W3,W4,W5,C23 ,S1,S2,T0,T1,T2,U0,U1,U2); \
    } while (0)


static void bashavx2_F0( u64 S[24] )
{
    u256 S1,S2,T0,T1,T2,U0,U1,U2;
    u256 W0 = LOADW( S + 0 );
    u256 W1 = LOADW( S + 4 );
    u256 W2 = LOADW( S + 8 );
    u256 W3 = LOADW( S + 12 );
    u256 W4 = LOADW( S + 16 );
    u256 W5 = LOADW( S + 20 );

    bashFP(W0,W1,W2,W3,W4,W5 ,S1,S2,T0,T1,T2,U0,U1,U2);

    STOREW( S + 0, W0 );
    STOREW( S + 4, W1 );
    STOREW( S + 8, W2 );
    STOREW( S + 12, W3 );
    STOREW( S + 16, W4 );
    STOREW( S + 20, W5 );
}

void bashavx2_F( octet block[ 192 ] )
{
    u64* s = (u64*)block;
#if (OCTET_ORDER == BIG_ENDIAN)
    u64Rev2( s, 24 );
#endif
    bashavx2_F0( s );
#if (OCTET_ORDER == BIG_ENDIAN)
    u64Rev2( s, 24 );
#endif
}

/*
*******************************************************************************
Хэширование
*******************************************************************************
*/

typedef struct
{
    u64 s[ 24 ];			/*< состояние */
    u64 s1[ 24 ];			/*< копия s */
    size_t block_len;	/*< длина блока */
    size_t filled;		/*< накоплено октетов в блоке */
} bashavx2__st;

size_t bashavx2_keep()
{
    return sizeof( bashavx2__st );
}

void bashavx2_Start( void* state, size_t l )
{
    bashavx2__st* s = (bashavx2__st*)state;
    ASSERT( l > 0 && l % 16 == 0 && l <= 256 );
    // s <- 0^{1536 - 64} || <l / 4>_{64}
    memSetZero( s->s, sizeof( s->s ) - 8 );
    s->s[ 23 ] = (u64)( l / 4 );
    // длина блока
    s->block_len = 192 - l / 2;
    // нет накопленнных данных
    s->filled = 0;
}

void bashavx2_StepH( const void* buf, size_t count, void* state )
{
    bashavx2__st* s = (bashavx2__st*)state;
    // есть накопленные данные?
    if( s->filled )
    {
        if( count < s->block_len - s->filled )
        {
            memCopy( (octet*)s->s + s->filled, buf, count );
            s->filled += count;
            return;
        }
        memCopy( (octet*)s->s + s->filled, buf, s->block_len - s->filled );
        count -= s->block_len - s->filled;
        buf = (const octet*)buf + s->block_len - s->filled;
#if (OCTET_ORDER == BIG_ENDIAN)
        u64Rev2( s->s, s->block_len / 8 );
#endif
        bashavx2_F0( s->s );
        s->filled = 0;
    }
    // цикл по полным блокам
    while( count >= s->block_len )
    {
        memCopy( s->s, buf, s->block_len );
#if (OCTET_ORDER == BIG_ENDIAN)
        u64Rev2( s->s, s->block_len / 8 );
#endif
        bashavx2_F0( s->s );
        buf = (const octet*)buf + s->block_len;
        count -= s->block_len;
    }
    // неполный блок?
    if( count )
        memCopy( s->s, buf, s->filled = count );
}

static void bashavx2_StepG_internal( size_t hash_len, void* state )
{
    bashavx2__st* s = (bashavx2__st*)state;
    // pre
    ASSERT( s->block_len + hash_len * 2 <= 192 );
    // создать копию s->s
    memCopy( s->s1, s->s, sizeof( s->s ) );
    // есть необработанные данные?
    if( s->filled )
    {
        memSetZero( (octet*)s->s1 + s->filled, s->block_len - s->filled );
        ( (octet*)s->s1 )[ s->filled ] = 0x40;
    }
    // дополнительный блок
    else
    {
        memSetZero( s->s1, s->block_len );
        ( (octet*)s->s1 )[ 0 ] = 0x40;
    }
    // последний шаг
    bashavx2_F0( s->s1 );
#if (OCTET_ORDER == BIG_ENDIAN)
    u64Rev2( s->s1, ( hash_len + 7 ) / 8 );
#endif
}

void bashavx2_StepG( octet hash[], size_t hash_len, void* state )
{
    bashavx2__st* s = (bashavx2__st*)state;
    bashavx2_StepG_internal( hash_len, state );
    memMove( hash, s->s1, hash_len );
}

bool_t bashavx2_StepV( const octet hash[], size_t hash_len, void* state )
{
    bashavx2__st* s = (bashavx2__st*)state;
    bashavx2_StepG_internal( hash_len, state );
    return memEq( hash, s->s1, hash_len );
}

err_t bashavx2_Hash( octet hash[], size_t l, const void* src, size_t count )
{
    bashavx2__st s;
    void* state = &s;
    // проверить входные данные
    if( l == 0 || l % 16 != 0 || l > 256 )
        return ERR_BAD_PARAMS;
    // вычислить хэш-значение
    bashavx2_Start( state, l );
    bashavx2_StepH( src, count, state );
    bashavx2_StepG( hash, l / 4, state );
    return ERR_OK;
}
