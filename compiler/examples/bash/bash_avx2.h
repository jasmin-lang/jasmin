/*
*******************************************************************************
\file bash_avx2.h
\brief STB 34.101.77 (bash): hashing algorithms
\project bee2 [cryptographic library]
\author (C) Sergey Agievich [agievich@{bsu.by|gmail.com}]
\author (C) Vlad Semenov [semenov.vlad.by@gmail.com]
\created 2014.07.15
\version 2016.04.23
\license This program is released under the GNU General Public License 
version 3. See Copyright Notices in bee2/info.h.
*******************************************************************************
*/

#ifndef __BEE2_BASH_AVX2_H
#define __BEE2_BASH_AVX2_H

#include <stddef.h>
typedef unsigned char octet;
typedef unsigned long long u64;
typedef int err_t;
typedef int bool_t;
#define ERR_OK 0
#define ERR_BAD_PARAMS 1

#ifdef __cplusplus
extern "C" {
#endif

void bashavx2_F(
	octet block[192]	/*!< [in/out] прообраз/образ */
);

err_t bashavx2_Hash(
	octet hash[],		/*!< [out] хэш-значение */
	size_t l,			/*!< [out] уровень стойкости */
	const void* src,	/*!< [in] данные */
	size_t count		/*!< [in] число октетов данных */
);

#define bashavx2_256Hash(hash, src, count) bashavx2_Hash(hash, 128, src, count)
#define bashavx2_384Hash(hash, src, count) bashavx2_Hash(hash, 192, src, count)
#define bashavx2_512Hash(hash, src, count) bashavx2_Hash(hash, 256, src, count)

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* __BEE2_BASH_H */
