/*
*******************************************************************************
\file bash.h
\brief STB 34.101.77 (bash): hashing algorithms
\project bee2 [cryptographic library]
\author (C) Sergey Agievich [agievich@{bsu.by|gmail.com}]
\created 2014.07.15
\version 2015.12.01
\license This program is released under the GNU General Public License 
version 3. See Copyright Notices in bee2/info.h.
*******************************************************************************
*/

#ifndef __BEE2_BASH_H
#define __BEE2_BASH_H

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

void bashF(
	octet block[192]	/*!< [in/out] прообраз/образ */
);

err_t bashHash(
	octet hash[],		/*!< [out] хэш-значение */
	size_t l,			/*!< [out] уровень стойкости */
	const void* src,	/*!< [in] данные */
	size_t count		/*!< [in] число октетов данных */
);

#define bash256Hash(hash, src, count) bashHash(hash, 128, src, count)
#define bash384Hash(hash, src, count) bashHash(hash, 192, src, count)
#define bash512Hash(hash, src, count) bashHash(hash, 256, src, count)

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* __BEE2_BASH_H */
