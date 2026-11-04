/*
 * fec.c - Forward Error Correction (Reed-Solomon over GF(256))
 *
 * Vandermonde-matrix based systematic erasure code.
 * GF(256) is defined by the primitive polynomial 0x11d (x^8+x^4+x^3+x^2+1).
 *
 * License: GPLv3
 */

#include "fec.h"
#include <string.h>
#include <stdlib.h>

/* ---- GF(256) arithmetic ------------------------------------------- */

#define GF_PRIM_POLY 0x11d
#define GF_SIZE      256

static uint8_t gf_exp[GF_SIZE * 2];
static uint8_t gf_log[GF_SIZE];
static int     gf_initialized = 0;

static void gf_init(void)
{
  int i;
  int x = 1;

  if (gf_initialized)
    return;

  memset(gf_log, 0, sizeof(gf_log));
  for (i = 0; i < GF_SIZE - 1; i++)
    {
      gf_exp[i] = (uint8_t)x;
      gf_log[x] = (uint8_t)i;
      x <<= 1;
      if (x & GF_SIZE)
        x ^= GF_PRIM_POLY;
    }
  /* Double the exp table to avoid overflow in multiplication. */
  for (i = 0; i < GF_SIZE - 1; i++)
    gf_exp[i + GF_SIZE - 1] = gf_exp[i];

  gf_initialized = 1;
}

static inline uint8_t gf_mul(uint8_t a, uint8_t b)
{
  if (a == 0 || b == 0)
    return 0;
  return gf_exp[gf_log[a] + gf_log[b]];
}

static inline uint8_t gf_pow(uint8_t a, int n)
{
  uint8_t r = 1;
  int i;
  for (i = 0; i < n; i++)
    r = gf_mul(r, a);
  return r;
}

static inline uint8_t gf_inv(uint8_t a)
{
  return gf_exp[GF_SIZE - 1 - gf_log[a]];
}

/* -------------------------------------------------------------------- */

/* Build the generator matrix: the first k rows form the identity,
 * the remaining r rows are the Vandermonde evaluation at x = 2^(i+1). */
static int build_matrix(uint8_t *gen, int k, int r)
{
  int i, j;
  uint8_t x, val;

  if (k <= 0 || r <= 0 || k > FEC_MAX_K || r > FEC_MAX_R)
    return -1;

  memset(gen, 0, (size_t)(k + r) * (size_t)k);

  /* identity rows */
  for (i = 0; i < k; i++)
    gen[i * k + i] = 1;

  /* vandermonde rows */
  for (i = 0; i < r; i++)
    {
      x = gf_pow(2, i + 1);
      val = 1;
      for (j = 0; j < k; j++)
        {
          gen[(k + i) * k + j] = val;
          val = gf_mul(val, x);
        }
    }

  return 0;
}

/* -------------------------------------------------------------------- */

int fec_encode(int k, int r,
               const uint8_t * const src[], uint8_t * const dst[],
               size_t block_len)
{
  uint8_t *gen;
  int i, j;
  size_t c;

  if (k <= 0 || r <= 0 || k > FEC_MAX_K || r > FEC_MAX_R)
    return -1;
  if (!src || !dst)
    return -1;

  gen = (uint8_t *)malloc((size_t)(k + r) * (size_t)k);
  if (!gen)
    return -1;
  gf_init();
  if (build_matrix(gen, k, r) != 0)
    {
      free(gen);
      return -1;
    }

  for (i = 0; i < r; i++)
    {
      const uint8_t *row = gen + (size_t)(k + i) * (size_t)k;
      for (c = 0; c < block_len; c++)
        {
          uint8_t acc = 0;
          for (j = 0; j < k; j++)
            {
              if (row[j] != 0 && src[j])
                acc ^= gf_mul(row[j], src[j][c]);
            }
          dst[i][c] = acc;
        }
    }

  free(gen);
  return 0;
}

/* -------------------------------------------------------------------- */

/* Gaussian elimination over GF(256): solve A * X = B.
 * A: n x n, B: n x block_len. On success the solution is in B.
 * Returns 0 on success, -1 if singular. */
static int gaussian_solve(uint8_t *A, uint8_t *B, int n, size_t block_len)
{
  int i, j, col, piv, t;
  uint8_t inv;
  size_t c;

  for (col = 0, i = 0; col < n && i < n; col++, i++)
    {
      /* find pivot */
      piv = -1;
      for (j = i; j < n; j++)
        {
          if (A[j * n + col] != 0)
            {
              piv = j;
              break;
            }
        }
      if (piv < 0)
        return -1; /* singular */

      if (piv != i)
        {
          for (j = 0; j < n; j++)
            {
              uint8_t tmp = A[i * n + j];
              A[i * n + j] = A[piv * n + j];
              A[piv * n + j] = tmp;
            }
          for (c = 0; c < block_len; c++)
            {
              uint8_t tmp = B[i * block_len + c];
              B[i * block_len + c] = B[piv * block_len + c];
              B[piv * block_len + c] = tmp;
            }
        }

      inv = gf_inv(A[i * n + col]);
      for (j = col; j < n; j++)
        A[i * n + j] = gf_mul(A[i * n + j], inv);
      for (c = 0; c < block_len; c++)
        B[i * block_len + c] = gf_mul(B[i * block_len + c], inv);

      /* eliminate other rows */
      for (j = 0; j < n; j++)
        {
          if (j != i && A[j * n + col] != 0)
            {
              uint8_t factor = A[j * n + col];
              for (t = col; t < n; t++)
                A[j * n + t] ^= gf_mul(factor, A[i * n + t]);
              for (c = 0; c < block_len; c++)
                B[j * block_len + c] ^= gf_mul(factor, B[i * block_len + c]);
            }
        }
    }

  return 0;
}

/* -------------------------------------------------------------------- */

int fec_decode(int k, int r,
               uint8_t * const dst[],
               const uint8_t * const recv[], const int idx[], int nrecv,
               size_t block_len)
{
  uint8_t *gen;
  uint8_t *A;
  uint8_t *B;
  int      i, s, rc;
  int      rows;

  if (k <= 0 || r < 0 || k > FEC_MAX_K || r > FEC_MAX_R)
    return -1;
  if (!dst || !recv || !idx)
    return -1;
  if (nrecv < k)
    return -1; /* not enough blocks to recover */

  gf_init();
  gen = (uint8_t *)malloc((size_t)(k + r) * (size_t)k);
  if (!gen)
    return -1;
  if (build_matrix(gen, k, r) != 0)
    {
      free(gen);
      return -1;
    }

  /* Use at most k received blocks: a square system is required. */
  rows = nrecv;
  if (rows > k)
    rows = k;

  A = (uint8_t *)malloc((size_t)rows * (size_t)rows);
  B = (uint8_t *)malloc((size_t)rows * block_len);
  if (!A || !B)
    {
      free(gen); free(A); free(B);
      return -1;
    }

  for (i = 0; i < rows; i++)
    {
      s = idx[i];
      if (s < 0 || s >= k + r)
        {
          free(gen); free(A); free(B);
          return -1;
        }
      memcpy(A + (size_t)i * (size_t)rows,
             gen + (size_t)s * (size_t)k, (size_t)k);
      if (recv[i])
        memcpy(B + (size_t)i * block_len, recv[i], block_len);
      else
        memset(B + (size_t)i * block_len, 0, block_len);
    }

  rc = gaussian_solve(A, B, rows, block_len);

  if (rc == 0)
    {
      for (i = 0; i < k; i++)
        {
          if (dst[i])
            memcpy(dst[i], B + (size_t)i * block_len, block_len);
        }
    }

  free(gen); free(A); free(B);

  return rc;
}