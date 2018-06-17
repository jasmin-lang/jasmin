/*
*******************************************************************************
\file bash.c
\brief STB 34.101.77 (bash): hashing algorithms
\project bee2 [cryptographic library]
\author (C) Sergey Agievich [agievich@{bsu.by|gmail.com}]
\author (C) Vlad Semenov [semenov.vlad.by@gmail.com]
\created 2014.07.15
\version 2015.12.09
\license This program is released under the GNU General Public License 
version 3. See Copyright Notices in bee2/info.h.
*******************************************************************************
*/

#include "bash.h"
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
static
void u64Rev2(u64 buf[], size_t count)
{
	while (count--)
		buf[count] = u64Rev(buf[count]);
}

/*
*******************************************************************************
Алгоритм bash-s

\remark На платформе x64 компилятор распознает циклические сдвиги u64RotHi 
и задействует команды rol / ror.

\remark На платформе x64 скорость работы зависит от числа пересылок через 
команду mov. Макрос bashS реализован так, чтобы уменьшить число пересылок.
Дальнейшие оптимизации связаны с использованием новых вспомогательных 
переменных.
*******************************************************************************
*/

#define bashS(w0, w1, w2, m1, n1, m2, n2, t0, t1, t2)\
	t2 = u64RotHi(w0, m1),\
	w0 ^= w1 ^ w2,\
	t1 = w1 ^ u64RotHi(w0, n1),\
	w1 = t1 ^ t2,\
	w2 ^= u64RotHi(w2, m2) ^ u64RotHi(t1, n2),\
	t1 = w0 | w2,\
	t2 = w0 & w1,\
	t0 = ~w2,\
	t0 |= w1,\
	w0 ^= t0,\
	w1 ^= t1,\
	w2 ^= t2\

/*
*******************************************************************************
Тактовые константы

Рассчитаны с помощью следующей программы:
\code
	const u64 A = 0xDC2BE1997FE0D8AE;
	u64 C[24];
	C[0] = 0x3BF5080AC8BA94B1;
	for (size_t t = 1; t < 24; ++t)
		C[t] = (C[t - 1] >> 1) ^ (A & 0 - (C[t - 1] & 1));
\endcode
*******************************************************************************
*/

static const u64 c1 =  0x3BF5080AC8BA94B1;
static const u64 c2 =  0xC1D1659C1BBD92F6;
static const u64 c3 =  0x60E8B2CE0DDEC97B;
static const u64 c4 =  0xEC5FB8FE790FBC13;
static const u64 c5 =  0xAA043DE6436706A7;
static const u64 c6 =  0x8929FF6A5E535BFD;
static const u64 c7 =  0x98BF1E2C50C97550;
static const u64 c8 =  0x4C5F8F162864BAA8;
static const u64 c9 =  0x262FC78B14325D54;
static const u64 c10 =  0x1317E3C58A192EAA;
static const u64 c11 = 0x098BF1E2C50C9755;
static const u64 c12 = 0xD8EE19681D669304;
static const u64 c13 = 0x6C770CB40EB34982;
static const u64 c14 = 0x363B865A0759A4C1;
static const u64 c15 = 0xC73622B47C4C0ACE;
static const u64 c16 = 0x639B115A3E260567;
static const u64 c17 = 0xEDE6693460F3DA1D;
static const u64 c18 = 0xAAD8D5034F9935A0;
static const u64 c19 = 0x556C6A81A7CC9AD0;
static const u64 c20 = 0x2AB63540D3E64D68;
static const u64 c21 = 0x155B1AA069F326B4;
static const u64 c22 = 0x0AAD8D5034F9935A;
static const u64 c23 = 0x0556C6A81A7CC9AD;
static const u64 c24 = 0xDE8082CD72DEBC78;

/*
*******************************************************************************
Перестановка P

Перестановка P переносит слово из позиции P(x) в позицию x.

Макросы Pi задают действие перестановки P^i. Значение Pi(x) указывает,
какое первоначальное слово будет в позиции x после i тактов.

\warning Рекурсия P_i(x) = P_1(P_{i - 1}(x)) в VS09 работает только
до глубины 4. Дальше препроцессор не справляется.
*******************************************************************************
*/

#define P0(x) x

#define P1(x)\
	((x < 8) ? 8 + (x + 2 * (x & 1) + 7) % 8 :\
		((x < 16) ? 8 + (x ^ 1) : (5 * x + 6) % 8))

#define P2(x) P1(P1(x))

#define P3(x)\
	(8 * (x / 8) + ( x % 8 + 4) % 8)

#define P4(x) P1(P3(x))
#define P5(x) P2(P3(x))

/*
*******************************************************************************
Такт

Макрос p задает расположение входных слов в ячейках массива s перед выполнением
такта i: в ячейке s[x] размещается первоначальное слово номер p(x).

Макрос p_next задает расположение входных слов перед выполнением такта i + 1.
*******************************************************************************
*/

#define bashR(s, p, p_next, i, t0, t1, t2)\
	bashS(s[p( 0)], s[p( 8)], s[p(16)],  8, 53, 14,  1, t0, t1, t2);\
	bashS(s[p( 1)], s[p( 9)], s[p(17)], 56, 51, 34,  7, t0, t1, t2);\
	bashS(s[p( 2)], s[p(10)], s[p(18)],  8, 37, 46, 49, t0, t1, t2);\
	bashS(s[p( 3)], s[p(11)], s[p(19)], 56,  3,  2, 23, t0, t1, t2);\
	bashS(s[p( 4)], s[p(12)], s[p(20)],  8, 21, 14, 33, t0, t1, t2);\
	bashS(s[p( 5)], s[p(13)], s[p(21)], 56, 19, 34, 39, t0, t1, t2);\
	bashS(s[p( 6)], s[p(14)], s[p(22)],  8,  5, 46, 17, t0, t1, t2);\
	bashS(s[p( 7)], s[p(15)], s[p(23)], 56, 35,  2, 55, t0, t1, t2);\
	s[p_next(23)] ^= c##i

/*
*******************************************************************************
Алгоритм bash-f (шаговая функция)
*******************************************************************************
*/

void bashF0(u64 s[24])
{
	register u64 t0;
	register u64 t1;
	register u64 t2;
	bashR(s, P0, P1,  1, t0, t1, t2);
	bashR(s, P1, P2,  2, t0, t1, t2);
	bashR(s, P2, P3,  3, t0, t1, t2);
	bashR(s, P3, P4,  4, t0, t1, t2);
	bashR(s, P4, P5,  5, t0, t1, t2);
	bashR(s, P5, P0,  6, t0, t1, t2);
	bashR(s, P0, P1,  7, t0, t1, t2);
	bashR(s, P1, P2,  8, t0, t1, t2);
	bashR(s, P2, P3,  9, t0, t1, t2);
	bashR(s, P3, P4, 10, t0, t1, t2);
	bashR(s, P4, P5, 11, t0, t1, t2);
	bashR(s, P5, P0, 12, t0, t1, t2);
	bashR(s, P0, P1, 13, t0, t1, t2);
	bashR(s, P1, P2, 14, t0, t1, t2);
	bashR(s, P2, P3, 15, t0, t1, t2);
	bashR(s, P3, P4, 16, t0, t1, t2);
	bashR(s, P4, P5, 17, t0, t1, t2);
	bashR(s, P5, P0, 18, t0, t1, t2);
	bashR(s, P0, P1, 19, t0, t1, t2);
	bashR(s, P1, P2, 20, t0, t1, t2);
	bashR(s, P2, P3, 21, t0, t1, t2);
	bashR(s, P3, P4, 22, t0, t1, t2);
	bashR(s, P4, P5, 23, t0, t1, t2);
	bashR(s, P5, P0, 24, t0, t1, t2);
	t0 = t1 = t2 = 0;
}

void bashF(octet block[192])
{
	u64* s = (u64*)block;
#if (OCTET_ORDER == BIG_ENDIAN)
	u64Rev2(s, 24);
#endif
  bashF0(s);
#if (OCTET_ORDER == BIG_ENDIAN)
	u64Rev2(s, 24);
#endif
}

/*
*******************************************************************************
Хэширование
*******************************************************************************
*/

typedef struct {
	u64 s[24];			/*< состояние */
	u64 s1[24];			/*< копия s */
	size_t block_len;	/*< длина блока */
	size_t filled;		/*< накоплено октетов в блоке */
} bash_st;

size_t bash_keep()
{
	return sizeof(bash_st);
}

void bashStart(void* state, size_t l)
{
	bash_st* s = (bash_st*)state;
	ASSERT(l > 0 && l % 16 == 0 && l <= 256);
	// s <- 0^{1536 - 64} || <l / 4>_{64}
	memSetZero(s->s, sizeof(s->s) - 8);
	s->s[23] = (u64)(l / 4);
	// длина блока
	s->block_len = 192 - l / 2;
	// нет накопленнных данных
	s->filled = 0;
}

void bashStepH(const void* buf, size_t count, void* state)
{
	bash_st* s = (bash_st*)state;
	// есть накопленные данные?
	if (s->filled)
	{
		if (count < s->block_len - s->filled)
		{
			memCopy((octet*)s->s + s->filled, buf, count);
			s->filled += count;
			return;
		}
		memCopy((octet*)s->s + s->filled, buf, s->block_len - s->filled);
		count -= s->block_len - s->filled;
		buf = (const octet*)buf + s->block_len - s->filled;
#if (OCTET_ORDER == BIG_ENDIAN)
		u64Rev2(s->s, s->block_len / 8);
#endif
		bashF0(s->s);
		s->filled = 0;
	}
	// цикл по полным блокам
	while (count >= s->block_len)
	{
		memCopy(s->s, buf, s->block_len);
#if (OCTET_ORDER == BIG_ENDIAN)
		u64Rev2(s->s, s->block_len / 8);
#endif
		bashF0(s->s);
		buf = (const octet*)buf + s->block_len;
		count -= s->block_len;
	}
	// неполный блок?
	if (count)
		memCopy(s->s, buf, s->filled = count);
}

static void bashStepG_internal(size_t hash_len, void* state)
{
	bash_st* s = (bash_st*)state;
	// pre
	ASSERT(s->block_len + hash_len * 2 <= 192);
	// создать копию s->s
	memCopy(s->s1, s->s, sizeof(s->s));
	// есть необработанные данные?
	if (s->filled)
	{
		memSetZero((octet*)s->s1 + s->filled, s->block_len - s->filled);
		((octet*)s->s1)[s->filled] = 0x40;
	}
	// дополнительный блок
	else
	{
		memSetZero(s->s1, s->block_len);
		((octet*)s->s1)[0] = 0x40;
	}
	// последний шаг
	bashF0(s->s1);
#if (OCTET_ORDER == BIG_ENDIAN)
	u64Rev2(s->s1, (hash_len + 7) / 8);
#endif
}

void bashStepG(octet hash[], size_t hash_len, void* state)
{
	bash_st* s = (bash_st*)state;
	bashStepG_internal(hash_len, state);
	memMove(hash, s->s1, hash_len);
}

bool_t bashStepV(const octet hash[], size_t hash_len, void* state)
{
	bash_st* s = (bash_st*)state;
	bashStepG_internal(hash_len, state);
	return memEq(hash, s->s1, hash_len);
}

err_t bashHash(octet hash[], size_t l, const void* src, size_t count)
{
	bash_st s;
	void* state = &s;
	// проверить входные данные
	if (l == 0 || l % 16 != 0 || l > 256)
		return ERR_BAD_PARAMS;
	// вычислить хэш-значение
	bashStart(state, l);
	bashStepH(src, count, state);
	bashStepG(hash, l / 4, state);
	return ERR_OK;
}
