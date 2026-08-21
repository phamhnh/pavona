/* Copyright zeroRISC Inc. */
/* Modified by Authors of "Towards ML-KEM & ML-DSA on OpenTitan" (https://eprint.iacr.org/2024/1192). */
/* Copyright "Towards ML-KEM & ML-DSA on OpenTitan" Authors. */
/* Modified by Ruben Niederhagen and Hoang Nguyen Hien Pham - authors of */
/* "Improving ML-KEM & ML-DSA on OpenTitan - Efficient Multiplication Vector Instructions for OTBN" */
/* (https://eprint.iacr.org/2025/2028). */
/* Copyright Ruben Niederhagen and Hoang Nguyen Hien Pham. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.text

#ifdef HARDENED
#define NSHARES 2
#else
#define NSHARES 1
#endif

#define N_WDR 16

/**
 * Decryption for the CPA-secure public-key encryption scheme underlying
 * ML-KEM.
 *
 * Recover the message from a ciphertext: decompress u and v, compute
 * m = v - s^T * u, and convert the result back into 32 bytes. When built with
 * HARDENED, the message is produced in Boolean-shared form by
 * masked_poly_tomsg.
 *
 * @param[in]  x10: dmem pointer to the input ciphertext
 * @param[in]  x11: dmem pointer to the input packed masked secret key
 * @param[out] x12: dmem pointer to the output message
 * @param[in]  x13: k, the security level
 * @param[in]  w31: all-zero register
 *
 * UNPROTECTED
 * clobbered registers: x2 to x5, x8 to x13, x18 to x19, x21 to x25,
 *                      w0 to w26, w30, acc, acch, mod
 * clobbered flag groups: FG0
 *
 * HARDENED
 * clobbered registers: x2 to x19, x21 to x25, x28 to x31, w0 to w26,
 *                      w28 to w29, acc, acch, mod
 * clobbered flag groups: FG0
 */
.globl indcpa_dec
.type indcpa_dec, @function
indcpa_dec:
  /* Save x3 to stack */
  addi x2, x2, -32
  sw   x3, 0(x2)
  addi x3, x2, 0

  addi x8, x10, 0
  addi x9, x11, 0
  addi x18, x12, 0
  addi x19, x13, 0

  /* Unpack sk and ct polynomial by polynomial. multiply them and accumulate
   * the result in m. */
  la x21, mpoly_sk
  la x22, poly_b
  la x23, mpoly_m
  la x24, twiddles_ntt
  la x25, twiddles_basemul

#ifndef HARDENED
  /* Unpack sk[0]. */
  addi x10, x9, 0
  addi x11, x21, 0 /* sk */
  jal  x1, poly_frombytes
  addi x9, x10, 0 /* Save address of sk to be unpacked later. */

  /* Unpack b.vec[0]. */
  bn.wsrr   w16, mod /* w16 = R | Q. */
  addi      x10, x8, 0 /* ct */
  addi      x11, x22, 0 /* b */
  addi      x12, x19, 0 /* k */
  jal       x1, poly_polyvec_decompress
  addi      x8, x10, 0 /* Save address of ct to be unpacked later. */

  /* Compute b = ntt(b). */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  addi       x10, x22, 0 /* b */
  addi       x11, x24, 0 /* twiddles_ntt */
  addi       x12, x10, 0
  jal        x1, ntt

  /* Compute m = b * sk. */
  addi x11, x21, 0 /* sk */
  addi x12, x25, 0 /* twiddles_basemul */
  addi x13, x23, 0 /* m */
  addi x10, x22, 0 /* poly_b */
  jal  x1, basemul

  /* Loop over j = 1,...,KYBER_K - 1. */
  addi x19, x19, -1 /* k - 1 */
  loop x19, 19
    /* Unpack sk.vec[j]. */
    addi x10, x9, 0 /* sk.vec[j]. */
    addi x11, x21, 0 /* sk */
    jal  x1, poly_frombytes
    addi x9, x10, 0 /* Save address of sk.vec[j + 1] to be unpacked later. */

    /* Unpack b.vec[j]. */
    /* w16 is still R | Q and mod is still 2*R | 2*Q. */
    addi x10, x8, 0 /* ct */
    addi x11, x22, 0 /* b */
    addi x12, x19, 1 /* k */
    jal  x1, poly_polyvec_decompress
    addi x8, x10, 0 /* Save address of ct to be unpacked later. */

    /* Compute b = ntt(b). */
    /* w16 is still R | Q and mod is still 2*R | 2*Q. */
    addi x10, x22, 0 /* b */
    addi x11, x24, 0 /* twiddles_ntt */
    addi x12, x10, 0
    jal  x1, ntt

    /* Compute m += b * sk. */
    /* w16 is still R | Q and mod is still 2*R | 2*Q. */
    addi x10, x22, 0 /* b */
    addi x11, x21, 0 /* sk */
    addi x12, x25, 0 /* twiddles_basemul */
    addi x13, x23, 0 /* m */
    jal  x1, basemul_acc
    nop
  endloop

  /* Compute m = intt(m). */
  addi    x10, x23, 0 /* m */
  la      x11, twiddles_intt
  addi    x12, x10, 0
  jal     x1, intt
  bn.wsrw mod, w16 /* Restore mod = R | Q */

  /* Unpack v. */
  addi x10, x8, 0 /* ct */
  la   x11, poly_v
  addi x12, x19, 1 /* k */
  jal  x1, poly_decompress

  /* Compute m = v - m. */
  la   x10, poly_v
  la   x11, mpoly_m
  addi x12, x11, 0
  jal  x1, poly_sub

  /* Compute r = poly_tomsg(m). */
  la   x10, mpoly_m
  addi x11, x18, 0 /* ptr_m */
  jal  x1, poly_tomsg
#else
  /* Unpack sk[0]. */
  addi x10, x9, 0
  addi x11, x21, 0 /* sk */
  loopi NSHARES, 4
    /* Whitening. */
    bn.xor  w0, w0, w0
    bn.xor  w1, w1, w1
    jal     x1, poly_frombytes
    nop
  endloop
  addi x9, x10, 0 /* Save address of sk to be unpacked later. */

  /* Refresh sk[0] arithmetic shares (MOD = R | Q here). */
  bn.wsrr w16, mod /* w16 = R | Q. */
  addi    x10, x21, 0
  addi    x12, x21, 0
  jal     x1, refreshmodq

  /* Unpack b.vec[0]. */
  addi      x10, x8, 0 /* ct */
  addi      x11, x22, 0 /* b */
  addi      x12, x19, 0 /* k */
  jal       x1, poly_polyvec_decompress
  addi      x8, x10, 0 /* Save address of ct to be unpacked later. */

  /* Compute b = ntt(b). */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  addi       x10, x22, 0 /* b */
  addi       x11, x24, 0 /* twiddles_ntt */
  addi       x12, x10, 0
  jal        x1, ntt

  /* Compute m = b * sk. */
  addi x11, x21, 0 /* sk */
  addi x12, x25, 0 /* twiddles_basemul */
  addi x13, x23, 0 /* m */
  loopi NSHARES, 4
    jal  x1, whitening
    addi x10, x22, 0 /* poly_b */
    jal  x1, basemul
    nop
  endloop

  /* Loop over j = 1,...,KYBER_K - 1. */
  addi x19, x19, -1 /* k - 1 */
  loop x19, 32
    /* Unpack sk.vec[j]. */
    addi x10, x9, 0 /* sk.vec[j]. */
    addi x11, x21, 0 /* sk */
    loopi NSHARES, 4
      /* Whitening. */
      bn.xor w0, w0, w0
      bn.xor w1, w1, w1
      jal    x1, poly_frombytes
      nop
    endloop
    addi x9, x10, 0 /* Save address of sk.vec[j + 1] to be unpacked later. */

    /* Refresh sk.vec[j] arithmetic shares. */
    bn.wsrw    mod, w16 /* MOD = R | Q. */
    addi       x10, x21, 0
    addi       x12, x21, 0
    jal        x1, refreshmodq
    bn.shv.16h w0, w16 << 1
    bn.wsrw    mod, w0 /* MOD = 2*R | 2*Q. */

    /* Unpack b.vec[j]. */
    /* w16 is still R | Q and mod is still 2*R | 2*Q. */
    addi x10, x8, 0 /* ct */
    addi x11, x22, 0 /* b */
    addi x12, x19, 1 /* k */
    jal  x1, poly_polyvec_decompress
    addi x8, x10, 0 /* Save address of ct to be unpacked later. */

    /* Compute b = ntt(b). */
    /* w16 is still R | Q and mod is still 2*R | 2*Q. */
    addi x10, x22, 0 /* b */
    addi x11, x24, 0 /* twiddles_ntt */
    addi x12, x10, 0
    jal  x1, ntt

    /* Compute m += b * sk. */
    addi x11, x21, 0 /* sk */
    addi x12, x25, 0 /* twiddles_basemul */
    /* w16 is still R | Q and mod is still 2*R | 2*Q. */
    addi x13, x23, 0 /* m */
    loopi NSHARES, 4
      jal  x1, whitening
      addi x10, x22, 0 /* b */
      jal  x1, basemul_acc
      nop
    endloop
    nop
  endloop

  /* Compute m = intt(m). */
  addi x10, x23, 0 /* m */
  la   x11, twiddles_intt
  addi x12, x10, 0
  loopi NSHARES, 3
    jal x1, whitening
    jal x1, intt
    nop
  endloop
  bn.wsrw mod, w16 /* Restore mod = R | Q */

  /* Unpack v. */
  addi x10, x8, 0 /* ct */
  la   x11, poly_v
  addi x12, x19, 1 /* k */
  jal  x1, poly_decompress

  /* Compute m = v - m. */
  la   x10, poly_v
  la   x11, mpoly_m
  addi x12, x11, 0
  jal  x1, poly_sub

  addi   x5, x0, NSHARES
  addi   x5, x5, -1 /* x5 = nshares - 1. */
  bn.xor w0, w0, w0
  loop x5, 5
    loopi N_WDR, 3
      bn.lid       x0, 0(x11)
      bn.subvm.16h w0, w31, w0
      bn.sid       x0, 0(x11++)
    endloop
    /* Whitening. */
    bn.xor w0, w0, w0
  endloop

  /* Compute r = masked_poly_tomsg(m). */
  la   x10, mpoly_m
  addi x12, x18, 0 /* ptr_m */
  jal  x1, masked_poly_tomsg

#endif

  /* Restore x2 and x3. */
  addi x2, x3, 0
  lw   x3, 0(x2)
  addi x2, x2, 32
  ret
