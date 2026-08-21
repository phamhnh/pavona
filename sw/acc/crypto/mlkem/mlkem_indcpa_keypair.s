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
#define NB_POLY 512

/* Config to start a SHA3_512 operation. */
#define SHA3_512_CFG 0x10

/**
 * Key generation for the CPA-secure public-key encryption scheme underlying
 * ML-KEM.
 *
 * Expand the seed into the matrix A and the noise polynomials s and e, compute
 * the public key t = A * s + e in NTT domain, and write both keys out in
 * packed form.
 *
 * @param[in]  x10: dmem pointer to the input seed
 *                  (KYBER_SYMBYTES = 32 bytes)
 * @param[out] x11: dmem pointer to the output packed public key
 * @param[out] x12: dmem pointer to the output packed secret key
 * @param[in]  x13: k, the security level
 *
 * UNPROTECTED
 * clobbered registers: x4 to x13, x18 to x28, w0 to w26, acc, acch, mod
 * clobbered flag groups: FG0
 *
 * HARDENED
 * clobbered registers: x2, x4 to x31, w0 to w30, acc, acch, mod
 * clobbered flag groups: FG0
 */
.globl indcpa_keypair
.type indcpa_keypair, @function
indcpa_keypair:
#ifndef HARDENED
  addi x9, x11, 0
  addi x18, x12, 0
  addi x19, x13, 0

  addi x4, x0, 2
  beq  x19, x4, _handle_k2_eta_1
  addi x20, x0, 2
  beq  x0, x0, _continue
_handle_k2_eta_1:
  addi x20, x0, 3
_continue:

  /* Compute G(seed || k). */
  /* Initialize a SHA3-512 operation. */
  addi    x11, x0, 33
  slli    x5, x11, 5
  addi    x5, x5, SHA3_512_CFG
  csrrw   x0, kmac_cfg, x5

  bn.lid  x0, 0(x10)
  bn.wsrw kmac_msg, w0
  addi    x5, x0, 1
  csrrw   x0, kmac_partial_write, x5
  la      x5, buf
  bn.xor  w0, w0, w0
  bn.sid  x0, 0(x5)
  sw      x13, 0(x5)
  bn.lid  x0, 0(x5)
  bn.wsrw kmac_msg, w0
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x5++)
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x5)

  /* Generate sk. */
  la     x8, buf
  la     x21, nonce
  bn.xor w0, w0, w0
  bn.sid x0, 0(x21)
  /* Prepare for generating sk[0]. */
  addi   x10, x8, 32 /* noiseseed */
  addi   x11, x21, 0 /* nonce */
  jal    x1, poly_getnoise_eta_init
  la     x22, mpolyvec_sk
  la     x23, twiddles_ntt

  addi x19, x19, -1 /* k - 1 */
  loop x19, 22
    /* Generate sk[i]. */
    addi   x10, x20, 0 /* ETA1 */
    addi   x11, x22, 0
    jal    x1, poly_getnoise_eta_1
    /* Prepare for generating sk[i + 1]. */
    addi   x10, x8, 32 /* noiseseed */
    addi   x11, x21, 0 /* nonce */
    lw     x5, 0(x11)
    addi   x5, x5, 1
    sw     x5, 0(x11)
    jal    x1, poly_getnoise_eta_init
    /* Compute sk[i] = ntt(sk[i]). */
    bn.wsrr    w16, mod /* w16 = R | Q */
    bn.shv.16h w0, w16 << 1
    bn.wsrw    mod, w0 /* mod = 2 * R | 2 * Q */
    addi       x10, x22, 0
    addi       x11, x23, 0
    addi       x12, x10, 0
    jal        x1, ntt
    bn.wsrw    mod, w16 /* Reset mod = R | Q. */
    /* Pack sk[i]. */
    addi   x10, x22, 0
    addi   x11, x18, 0
    jal    x1, poly_tobytes
    /* Update addresses. */
    addi   x22, x10, 0 /* Point to sk[i + 1]. */
    addi   x18, x11, 0 /* Point to next slot for packed sk. */
  endloop

  /* Generate sk[k - 1]. */
  addi   x10, x20, 0 /* ETA1 */
  addi   x11, x22, 0
  jal    x1, poly_getnoise_eta_1

  /* Compute sk[k - 1] = ntt(sk[k - 1]). */
  bn.wsrr    w16, mod /* w16 = R | Q */
  bn.shv.16h w0, w16 << 1
  bn.wsrw    mod, w0 /* mod = 2 * R | 2 * Q */
  addi       x10, x22, 0
  addi       x11, x23, 0
  addi       x12, x10, 0
  jal        x1, ntt
  bn.wsrw    mod, w16 /* Reset mod = R | Q. */

  /* Prepare for generating a[0][0]. */
  addi   x10, x8, 0 /* publicseed */
  la     x11, seed_ij
  bn.xor w0, w0, w0
  bn.sid x0, 0(x11)
  jal    x1, poly_gen_matrix_init

  /* Pack sk[k - 1]. */
  addi   x10, x22, 0
  addi   x11, x18, 0
  jal    x1, poly_tobytes

  /* Save current addresses of sk. */
  la x5, dptr_sk
  sw x11, 0(x5)

  /* The following block will do:
   *  - (1) generate a[i][0],
   *  - (2) compute pk = a[i][0] * sk[0],
   *  - (3) generate a[i][j],
   *  - (4) compute pk += a[i][j] * sk[j],
   *  - (5) repeat (3) + (4) for j = 1,...,k-1.
   *  - (6) compute pk = poly_tomont(pk),
   *  - (7) generate e[i],
   *  - (8) compute e[i] = ntt(e[i]),
   *  - (9) compute pk += e[i],
   *  - (10) pack pk,
   *  - (11) repeat (1) to (10) for i = 0,..,k-1.*/

  la   x21, nonce
  la   x22, mpolyvec_sk
  la   x23, twiddles_basemul
  la   x24, seed_ij
  la   x25, poly_at /* also poly_e */
  la   x26, mpoly_pk

  addi x18, x19, -1 /* k - 2 (x19 = k - 1) */
  addi x5, x0, 0x0100
  sub  x27, x5, x19 /* 0x0100 - (k - 1) */

  loop x19, 80
    /* Generate a[i][0]. */
    addi x11, x25, 0
    jal  x1, poly_gen_matrix

    /* Prepare for generating a[i][1]. */
    addi x10, x8, 0
    addi x11, x24, 0
    lw   x5, 0(x11)
    addi x5, x5, 1
    sw   x5, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute pk = a * sk[0]. */
    bn.wsrr    w16, mod /* w16 = R | Q */
    bn.shv.16h w0, w16 << 1
    bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
    addi       x10, x25, 0
    la         x22, mpolyvec_sk
    addi       x11, x22, 0
    addi       x12, x23, 0
    addi       x13, x26, 0
    jal        x1, basemul
    addi       x22, x11, 0 /* Point to sk[1]. */

    /* Skip the middle columns when k = 2 (x18 = k - 2 = 0); a hardware
     * loop must have a non-zero iteration count. */
    beq  x18, x0, _skip_inner_cols
    loop x18, 14
      /* Generate a[i][j]. */
      addi x11, x25, 0
      jal  x1, poly_gen_matrix

      /* Prepare for generating a[i][j + 1]. */
      addi x10, x8, 0
      addi x11, x24, 0
      lw   x5, 0(x11)
      addi x5, x5, 1
      sw   x5, 0(x11)
      jal  x1, poly_gen_matrix_init

      /* Compute pk += a * sk[j]. */
      addi x10, x25, 0
      addi x11, x22, 0
      addi x12, x23, 0
      addi x13, x26, 0
      jal  x1, basemul_acc
      addi x22, x11, 0 /* Point to sk[j + 1]. */
    endloop
    _skip_inner_cols:

    /* Generate a[i][k - 1]. */
    addi x11, x25, 0
    jal  x1, poly_gen_matrix

    /* Prepare for generating e[i]. */
    addi x10, x8, 32
    addi x11, x21, 0
    lw   x5, 0(x11)
    addi x5, x5, 1
    sw   x5, 0(x11)
    jal  x1, poly_getnoise_eta_init

    /* Compute pk += a * sk[k - 1]. */
    addi    x10, x25, 0
    addi    x11, x22, 0
    addi    x12, x23, 0
    addi    x13, x26, 0
    jal     x1, basemul_acc
    bn.wsrw mod, w16 /* Restore mod = R | Q. */

    /* Generate e[i]. */
    addi x10, x20, 0 /* ETA1 */
    la   x11, mpoly_e
    jal  x1, poly_getnoise_eta_1

    /* Prepare for generating a[i + 1][0]. */
    addi x10, x8, 0
    addi x11, x24, 0
    lw   x5, 0(x11)
    add  x5, x5, x27
    sw   x5, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute pk = tomont(pk). */
    addi x10, x26, 0
    jal  x1, poly_tomont

    /* Compute e[i] = ntt(e[i]). */
    bn.wsrr    w16, mod
    bn.shv.16h w0, w16 << 1
    bn.wsrw    mod, w0
    la         x10, mpoly_e
    la         x11, twiddles_ntt
    addi       x12, x10, 0
    jal        x1, ntt
    bn.wsrw    mod, w16

    /* Compute pk += e[i]. */
    addi x10, x26, 0
    la   x11, mpoly_e
    addi x12, x26, 0
    jal  x1, poly_add

    /* Pack pk. */
    addi x10, x26, 0
    addi x11, x9, 0
    jal  x1, poly_tobytes
    addi x9, x11, 0 /* Point to next slot for packed pk. */
  endloop

  /* Generate a[k - 1][0]. */
  addi x11, x25, 0
  jal  x1, poly_gen_matrix

  /* Prepare for generating a[k - 1][1]. */
  addi x10, x8, 0
  addi x11, x24, 0
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compute pk = a * sk[0]. */
  bn.wsrr    w16, mod /* w16 = R | Q */
  bn.shv.16h w0, w16 << 1
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  addi       x10, x25, 0
  la         x22, mpolyvec_sk
  addi       x11, x22, 0
  addi       x12, x23, 0
  addi       x13, x26, 0
  jal        x1, basemul
  addi       x22, x11, 0 /* Point to sk[1]. */

  /* Skip the middle columns when k = 2 (x18 = k - 2 = 0); a hardware
   * loop must have a non-zero iteration count. */
  beq  x18, x0, _skip_inner_cols_tail
  loop x18, 14
    /* Generate a[k - 1][j]. */
    addi x11, x25, 0
    jal  x1, poly_gen_matrix

    /* Prepare for generating a[k - 1][j + 1]. */
    addi x10, x8, 0
    addi x11, x24, 0
    lw   x5, 0(x11)
    addi x5, x5, 1
    sw   x5, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute pk += a * sk[j]. */
    addi x10, x25, 0
    addi x11, x22, 0
    addi x12, x23, 0
    addi x13, x26, 0
    jal  x1, basemul_acc
    addi x22, x11, 0 /* Point to sk[j + 1]. */
  endloop
  _skip_inner_cols_tail:

  /* Generate a[k - 1][k - 1]. */
  addi x11, x25, 0
  jal  x1, poly_gen_matrix

  /* Prepare for generating e[k - 1]. */
  addi x10, x8, 32
  addi x11, x21, 0
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, poly_getnoise_eta_init

  /* Compute pk += a * sk[k - 1]. */
  addi    x10, x25, 0
  addi    x11, x22, 0
  addi    x12, x23, 0
  addi    x13, x26, 0
  jal     x1, basemul_acc
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Generate e[k - 1]. */
  addi x10, x20, 0 /* ETA1 */
  la   x11, mpoly_e
  jal  x1, poly_getnoise_eta_1

  /* Compute pk = tomont(pk). */
  addi x10, x26, 0
  jal  x1, poly_tomont

  /* Compute e[k - 1] = ntt(e[k - 1]). */
  bn.wsrr    w16, mod
  bn.shv.16h w0, w16 << 1
  bn.wsrw    mod, w0
  la         x10, mpoly_e
  la         x11, twiddles_ntt
  addi       x12, x10, 0
  jal        x1, ntt
  bn.wsrw    mod, w16

  /* Compute pk += e[k - 1]. */
  addi x10, x26, 0
  la   x11, mpoly_e
  addi x12, x26, 0
  jal  x1, poly_add

  /* Pack pk. */
  addi x10, x26, 0
  addi x11, x9, 0
  jal  x1, poly_tobytes


_handle_common:

  /* Save publicseed. */
  la     x5, buf
  bn.lid x0, 0(x5)
  bn.sid x0, 0(x11)
  ret

#else
  addi x9, x11, 0
  addi x18, x12, 0
  addi x19, x13, 0

  addi x4, x0, 2
  beq  x19, x4, _handle_k2_eta_1
  addi x20, x0, 2
  beq  x0, x0, _continue
_handle_k2_eta_1:
  addi x20, x0, 3
_continue:

  /* Compute G(seed || k). */
  /* Initialize a SHA3-512 operation. */
  addi    x11, x0, 33
  slli    x5, x11, 5
  addi    x5, x5, SHA3_512_CFG
  addi    x6, x0, 1
  slli    x6, x6, 20
  add     x5, x5, x6
  csrrw   x0, kmac_cfg, x5

  bn.xor  w0, w0, w0 /* Whitening. */
  bn.lid  x0, 0(x10++)
  bn.wsrw kmac_msg, w0
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.lid  x0, 0(x10)
  bn.wsrw kmac_msg1, w0
  addi    x5, x0, 1
  csrrw   x0, kmac_partial_write, x5
  la      x5, buf
  bn.xor  w0, w0, w0
  bn.sid  x0, 0(x5)
  sw      x13, 0(x5)
  bn.lid  x0, 0(x5)
  bn.wsrw kmac_msg, w0
  bn.xor  w0, w0, w0
  bn.wsrw kmac_msg1, w0
  /* Read publicseed. */
  bn.wsrr w0, kmac_digest
  bn.wsrr w1, kmac_digest1
  bn.xor  w0, w0, w1
  bn.sid  x0, 0(x5++)
  /* Read noiseseed. */
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x5++)
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.wsrr w0, kmac_digest1
  bn.sid  x0, 0(x5++)

  /* Generate sk. */
  la     x8, buf
  la     x21, nonce
  bn.xor w0, w0, w0
  bn.sid x0, 0(x21)
  /* Prepare for generating sk[0]. */
  addi   x10, x8, 32 /* noiseseed */
  addi   x11, x21, 0 /* nonce */
  jal    x1, masked_poly_getnoise_eta_init
  la     x22, mpolyvec_sk
  la     x23, twiddles_ntt

  addi x19, x19, -1 /* k - 1 */
  loop x19, 29
    /* Generate sk[i]. */
    addi   x10, x20, 0 /* ETA1 */
    addi   x11, x22, 0
    jal    x1, masked_poly_getnoise_eta_1

    /* Prepare for generating sk[i + 1]. */
    addi   x10, x8, 32 /* noiseseed */
    addi   x11, x21, 0 /* nonce */
    lw     x5, 0(x11)
    addi   x5, x5, 1
    sw     x5, 0(x11)
    jal    x1, masked_poly_getnoise_eta_init

    /* Compute sk[i] = ntt(sk[i]). */
    bn.wsrr    w16, mod /* w16 = R | Q */
    bn.shv.16h w0, w16 << 1
    bn.wsrw    mod, w0 /* mod = 2 * R | 2 * Q */
    addi       x10, x22, 0
    addi       x11, x23, 0
    addi       x12, x10, 0
    loopi NSHARES, 3
      jal x1, whitening
      jal x1, ntt
      nop
    endloop
    bn.wsrw mod, w16 /* Reset mod = R | Q. */

    /* Pack sk[i]. */
    addi   x10, x22, 0
    addi   x11, x18, 0
    loopi NSHARES, 4
      /* Whitening. */
      bn.xor w0, w0, w0
      bn.xor w1, w1, w1
      jal x1, poly_tobytes
      nop
    endloop

    /* Update addresses. */
    addi x22, x10, 0 /* Point to sk[i + 1]. */
    addi x18, x11, 0 /* Point to next slot for packed sk. */
  endloop

  /* Generate sk[k - 1]. */
  addi   x10, x20, 0 /* ETA1 */
  addi   x11, x22, 0
  jal    x1, masked_poly_getnoise_eta_1

  /* Compute sk[k - 1] = ntt(sk[k - 1]). */
  bn.wsrr    w16, mod /* w16 = R | Q */
  bn.shv.16h w0, w16 << 1
  bn.wsrw    mod, w0 /* mod = 2 * R | 2 * Q */

  addi x10, x22, 0
  addi x11, x23, 0
  addi x12, x10, 0
  loopi NSHARES, 3
    jal x1, whitening
    jal x1, ntt
    nop
  endloop
  bn.wsrw mod, w16 /* Reset mod = R | Q. */

  /* Prepare for generating a[0][0]. */
  addi   x10, x8, 0 /* publicseed */
  la     x11, seed_ij
  bn.xor w0, w0, w0
  bn.sid x0, 0(x11)
  jal    x1, poly_gen_matrix_init

  /* Pack sk[k - 1]. */
  addi x10, x22, 0
  addi x11, x18, 0
  loopi NSHARES, 4
    /* Whitening. */
    bn.xor w0, w0, w0
    bn.xor w1, w1, w1
    jal    x1, poly_tobytes
    nop
  endloop

  /* Save current addresses of sk. */
  la x5, dptr_sk
  sw x11, 0(x5)

  /* The following block will do:
   *  - (1) generate a[i][0],
   *  - (2) compute pk = a[i][0] * sk[0],
   *  - (3) generate a[i][j],
   *  - (4) compute pk += a[i][j] * sk[j],
   *  - (5) repeat (3) + (4) for j = 1,...,k-1.
   *  - (6) compute pk = poly_tomont(pk),
   *  - (7) generate e[i],
   *  - (8) compute e[i] = ntt(e[i]),
   *  - (9) compute pk += e[i],
   *  - (10) pack pk,
   *  - (11) repeat (1) to (10) for i = 0,..,k-1.*/

  la   x21, nonce
  la   x22, mpolyvec_sk
  la   x23, twiddles_basemul
  la   x24, seed_ij
  la   x25, poly_at /* also poly_e */
  la   x26, mpoly_pk

  addi x18, x19, -1 /* k - 2 (x19 = k - 1) */
  addi x5, x0, 0x0100
  sub  x27, x5, x19 /* 0x0100 - (k - 1) */

  loop x19, 111
    /* Generate a[i][0]. */
    addi x11, x25, 0
    jal  x1, poly_gen_matrix

    /* Prepare for generating a[i][1]. */
    addi x10, x8, 0
    addi x11, x24, 0
    lw   x5, 0(x11)
    addi x5, x5, 1
    sw   x5, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute pk = a * sk[0]. */
    bn.wsrr    w16, mod /* w16 = R | Q */
    bn.shv.16h w0, w16 << 1
    bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */

    addi x10, x25, 0
    la   x11, mpolyvec_sk
    addi x12, x23, 0
    addi x13, x26, 0
    loopi NSHARES, 3
      jal  x1, whitening
      jal  x1, basemul
      addi x10, x25, 0
    endloop
    addi x22, x11, 0 /* Point to sk[1]. */

    /* Skip the middle columns when k = 2 (x18 = k - 2 = 0); a hardware
     * loop must have a non-zero iteration count. */
    beq  x18, x0, _skip_inner_cols
    loop x18, 17
      /* Generate a[i][j]. */
      addi x11, x25, 0
      jal  x1, poly_gen_matrix

      /* Prepare for generating a[i][j + 1]. */
      addi x10, x8, 0
      addi x11, x24, 0
      lw   x5, 0(x11)
      addi x5, x5, 1
      sw   x5, 0(x11)
      jal  x1, poly_gen_matrix_init

      /* Compute pk += a * sk[j]. */
      addi x10, x25, 0
      addi x11, x22, 0
      addi x12, x23, 0
      addi x13, x26, 0
      loopi NSHARES, 3
        jal  x1, whitening
        jal  x1, basemul_acc
        addi x10, x25, 0
      endloop
      addi x22, x11, 0 /* Point to sk[j + 1]. */
    endloop
    _skip_inner_cols:

    /* Generate a[i][k - 1]. */
    addi x11, x25, 0
    jal  x1, poly_gen_matrix

    /* Prepare for generating e[i]. */
    addi x10, x8, 32
    addi x11, x21, 0
    lw   x5, 0(x11)
    addi x5, x5, 1
    sw   x5, 0(x11)
    jal  x1, masked_poly_getnoise_eta_init

    /* Compute pk += a * sk[k - 1]. */
    addi x10, x25, 0
    addi x11, x22, 0
    addi x12, x23, 0
    addi x13, x26, 0
    loopi NSHARES, 3
      jal  x1, whitening
      jal  x1, basemul_acc
      addi x10, x25, 0
    endloop
    bn.wsrw mod, w16 /* Restore mod = R | Q. */

    /* Generate e[i]. */
    addi x10, x20, 0 /* ETA1 */
    la   x11, mpoly_e
    jal  x1, masked_poly_getnoise_eta_1

    /* Prepare for generating a[i + 1][0]. */
    addi x10, x8, 0
    addi x11, x24, 0
    lw   x5, 0(x11)
    add  x5, x5, x27
    sw   x5, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute pk = tomont(pk). */
    addi x10, x26, 0
    loopi NSHARES, 4
      /* Whitening. */
      bn.xor w0, w0, w0
      bn.xor w1, w1, w1
      jal    x1, poly_tomont
      nop
    endloop

    /* Compute e[i] = ntt(e[i]). */
    bn.wsrr    w16, mod
    bn.shv.16h w0, w16 << 1
    bn.wsrw    mod, w0

    la   x10, mpoly_e
    la   x11, twiddles_ntt
    addi x12, x10, 0
    loopi NSHARES, 3
      jal x1, whitening
      jal x1, ntt
      nop
    endloop

    /* Compute pk += e[i]. */
    addi x10, x26, 0
    la   x11, mpoly_e
    addi x12, x26, 0
    loopi NSHARES, 4
      /* Whitening. */
      bn.xor w0, w0, w0
      bn.xor w1, w1, w1
      jal    x1, poly_add
      nop
    endloop

    /* Unmask pk. */
    addi x4, x0, 1
    addi x5, x26, 0
    addi x6, x0, NSHARES
    addi x6, x6, -1
    loopi N_WDR, 7
      addi   x7, x5, NB_POLY
      bn.lid x0, 0(x5)
      loop x6, 3
        bn.lid       x4, 0(x7)
        bn.addvm.16h w0, w0, w1
        addi         x7, x7, NB_POLY
      endloop
      bn.sid x0, 0(x5++)
    endloop

    bn.wsrw mod, w16

    /* Pack pk. */
    addi x10, x26, 0
    addi x11, x9, 0
    jal  x1, poly_tobytes
    addi x9, x11, 0 /* Point to next slot for packed pk. */
  endloop

  /* Generate a[k - 1][0]. */
  addi x11, x25, 0
  jal  x1, poly_gen_matrix

  /* Prepare for generating a[k - 1][1]. */
  addi x10, x8, 0
  addi x11, x24, 0
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compute pk = a * sk[0]. */
  bn.wsrr    w16, mod /* w16 = R | Q */
  bn.shv.16h w0, w16 << 1
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */

  addi x10, x25, 0
  la   x11, mpolyvec_sk
  addi x12, x23, 0
  addi x13, x26, 0
  loopi NSHARES, 3
    jal  x1, whitening
    jal  x1, basemul
    addi x10, x25, 0
  endloop
  addi x22, x11, 0 /* Point to sk[1]. */

  /* Skip the middle columns when k = 2 (x18 = k - 2 = 0); a hardware
   * loop must have a non-zero iteration count. */
  beq  x18, x0, _skip_inner_cols_tail
  loop x18, 17
    /* Generate a[k - 1][j]. */
    addi x11, x25, 0
    jal  x1, poly_gen_matrix

    /* Prepare for generating a[k - 1][j + 1]. */
    addi x10, x8, 0
    addi x11, x24, 0
    lw   x5, 0(x11)
    addi x5, x5, 1
    sw   x5, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute pk += a * sk[j]. */
    addi x10, x25, 0
    addi x11, x22, 0
    addi x12, x23, 0
    addi x13, x26, 0
    loopi NSHARES, 3
      jal  x1, whitening
      jal  x1, basemul_acc
      addi x10, x25, 0
    endloop
    addi x22, x11, 0 /* Point to sk[j + 1]. */
  endloop
  _skip_inner_cols_tail:

  /* Generate a[k - 1][k - 1]. */
  addi x11, x25, 0
  jal  x1, poly_gen_matrix

  /* Prepare for generating e[k - 1]. */
  addi x10, x8, 32
  addi x11, x21, 0
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, masked_poly_getnoise_eta_init

  /* Compute pk += a * sk[k - 1]. */
  addi x10, x25, 0
  addi x11, x22, 0
  addi x12, x23, 0
  addi x13, x26, 0
  loopi NSHARES, 3
    jal  x1, whitening
    jal  x1, basemul_acc
    addi x10, x25, 0
  endloop
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Generate e[k - 1]. */
  addi x10, x20, 0 /* ETA1 */
  la   x11, mpoly_e
  jal  x1, masked_poly_getnoise_eta_1

  /* Compute pk = tomont(pk). */
  addi x10, x26, 0
  loopi NSHARES, 4
    /* Whitening. */
    bn.xor w0, w0, w0
    bn.xor w1, w1, w1
    jal    x1, poly_tomont
    nop
  endloop

  /* Compute e[k - 1] = ntt(e[k - 1]). */
  bn.wsrr    w16, mod
  bn.shv.16h w0, w16 << 1
  bn.wsrw    mod, w0

  la   x10, mpoly_e
  la   x11, twiddles_ntt
  addi x12, x10, 0
  loopi NSHARES, 3
    jal x1, whitening
    jal x1, ntt
    nop
  endloop

  /* Compute pk += e[k - 1]. */
  addi x10, x26, 0
  la   x11, mpoly_e
  addi x12, x26, 0
  loopi NSHARES, 4
    /* Whitening. */
    bn.xor w0, w0, w0
    bn.xor w1, w1, w1
    jal    x1, poly_add
    nop
  endloop

  /* Unmask pk. */
  addi x4, x0, 1
  addi x5, x26, 0
  addi x6, x0, NSHARES
  addi x6, x6, -1
  loopi N_WDR, 7
    addi   x7, x5, NB_POLY
    bn.lid x0, 0(x5)
    loop x6, 3
      bn.lid       x4, 0(x7)
      bn.addvm.16h w0, w0, w1
      addi         x7, x7, NB_POLY
    endloop
    bn.sid x0, 0(x5++)
  endloop

  bn.wsrw mod, w16

  /* Pack pk. */
  addi x10, x26, 0
  addi x11, x9, 0
  jal  x1, poly_tobytes


_handle_common:

  /* Save publicseed. */
  la     x5, buf
  bn.lid x0, 0(x5)
  bn.sid x0, 0(x11)
  ret

#endif
