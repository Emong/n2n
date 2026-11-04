/*
 * fec.h - Forward Error Correction (Reed-Solomon over GF(256))
 *
 * Implements a Vandermonde-matrix based erasure code so that a receiver
 * can reconstruct all k data blocks of a group whenever at least k of the
 * (k + r) transmitted blocks are received.
 *
 * License: GPLv3 (same as the rest of n2n)
 */

#ifndef _FEC_H_
#define _FEC_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define FEC_MAX_K 16   /* maximum number of data blocks per group */
#define FEC_MAX_R 8    /* maximum number of parity blocks per group */

/* Encode r parity blocks from k data blocks.
 *
 * src  : array of k pointers, each block_len bytes (data blocks)
 * dst  : array of r pointers, each block_len bytes (output parity blocks)
 * returns 0 on success, -1 on invalid parameters.
 */
int fec_encode(int k, int r,
               const uint8_t * const src[], uint8_t * const dst[],
               size_t block_len);

/* Recover all k data blocks from at least k received blocks.
 *
 * recv : array of nrecv pointers, the actually received blocks
 * idx  : array of nrecv wire indices corresponding to recv[]
 * dst  : array of k pointers for the recovered data blocks (block_len each)
 * returns 0 on success, -1 on failure (singular matrix / bad params).
 */
int fec_decode(int k, int r,
               uint8_t * const dst[],
               const uint8_t * const recv[], const int idx[], int nrecv,
               size_t block_len);

#ifdef __cplusplus
}
#endif

#endif /* _FEC_H_ */