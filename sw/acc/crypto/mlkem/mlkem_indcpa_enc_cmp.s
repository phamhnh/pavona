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

/**
 * Re-encryption and ciphertext comparison for the decapsulation check.
 *
 * Encrypt a Boolean-shared message exactly as indcpa_enc does, but compare
 * each compressed ciphertext component against the given ciphertext instead of
 * writing it out. This lets crypto_kem_dec verify the re-encryption without
 * ever materializing the re-encrypted ciphertext in memory.
 *
 * @param[in]  x10: dmem pointer to the input Boolean-shared message
 * @param[in]  x11: dmem pointer to the input packed public key
 * @param[in]  x12: dmem pointer to the input coins (32 bytes)
 * @param[in]  x13: dmem pointer to the input ciphertext to compare against
 * @param[in]  x14: nshares, the number of shares of the message
 * @param[in]  x15: k, the security level
 * @param[in]  w31: all-zero register
 * @param[out] w0: 1 if the ciphertexts match, 0 otherwise
 *
 * UNPROTECTED
 * clobbered registers: x2 to x13, x18 to x28, w0 to w26, w30, acc, acch, mod
 * clobbered flag groups: FG0
 *
 * HARDENED
 * clobbered registers: x2 to x24, x26 to x31, w0 to w30, acc, acch, mod
 * clobbered flag groups: FG0
 */

.globl indcpa_enc_cmp
.type indcpa_enc_cmp, @function
indcpa_enc_cmp:
  /* Save x3 to stack */
  addi x2, x2, -32
  sw   x3, 0(x2)
  addi x3, x2, 0

  addi x9, x11, 0
  addi x18, x12, 0
  addi x19, x13, 0
  addi x20, x14, 0
  addi x21, x15, 0

#ifndef HARDENED
  addi x4, x0, 4
  beq  x21, x4, _compute_k4_consts
_compute_kn4_consts:
  addi x26, x0, 128 /* dv * 32 = 4 * 32 */
  addi x27, x0, 320 /* du * 32 = 10 * 32 */
  beq  x0, x0, _continue
_compute_k4_consts:
  addi x26, x0, 160 /* dv * 32 = 5 * 32 */
  addi x27, x0, 352 /* du * 32 = 11 * 32 */
_continue:
  /* Adjust stack for packed re-encrypted ciphertext and comparison result. */
  sub  x2, x2, x27
  addi x25, x2, 0 /* ptr_packed_ct */
  addi x2, x2, -32 /* ptr_r */

  /* Compute k = onebitdecompress(m, nshares). */
  /* x10 is already ptr_m. */
  la   x11, mpoly_k
  jal  x1, poly_frommsg

  /* The following block will:
   *  (1) unpack pk[i],
   *  (2) sample x2[i],
   *  (3) compute x2[i] = ntt(x2[i]),
   *  (4) compute v += pk[i] * x2[i],
   *  (5) compute v = intt(v),
   *  (6) compute v += k
   *  (7) sample epp
   *  (8) compute v += epp
   *  (9) compare v and ct, output to r. */
  /**************************************************************************/
  addi x4, x0, 2
  beq  x21, x4, _handle_k2_eta_1
_handle_kn2_eta_1:
  addi x22, x0, 2 /* ETA1 */
  beq  x0, x0, _continue_compute_v
_handle_k2_eta_1:
  addi x22, x0, 3 /* ETA1 */

_continue_compute_v:

  /* Prepare for initial `poly_getnoise_eta_1` call: generate x2. */
  addi   x10, x18, 0 /* coins */
  la     x11, nonce
  bn.xor w0, w0, w0
  bn.sid x0, 0(x11)
  jal    x1, poly_getnoise_eta_init

  /* Unpack pk[0]. */
  addi x10, x9, 0
  la   x11, poly_pk
  jal  x1, poly_frombytes
  addi x9, x10, 0 /* Save address of pk to be unpacked later. */

  /* Generate x2[0]. */
  addi x10, x22, 0 /* ETA1 */
  la   x11, mpolyvec_sp
  jal  x1, poly_getnoise_eta_1

  /* Prepare for generating x2[1]. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, poly_getnoise_eta_init

  /* Compute x2[0] = ntt(x2[0]). */
  bn.wsrr    w16, mod /* w16 = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x10, mpolyvec_sp
  la         x11, twiddles_ntt
  add        x12, x10, 0
  jal        x1, ntt

  /* Compute v = pk[0] * x2[0]. */
  la      x10, poly_pk
  la      x11, mpolyvec_sp
  la      x12, twiddles_basemul
  la      x13, mpoly_v
  jal     x1, basemul
  addi    x24, x11, 0 /* Point to x2[1]. */
  bn.wsrw mod, w16 /* Reset mod = R | Q */

  /* At this point:
   *  - x9 points to packed pk.
   *  - x18 points to coins (for cbd).
   *  - x19 points to ct (for later).
   *  - x20 = nshares.
   *  - x21 is the security level k.
   *  - x22 is ETA1.
   *  - x23 points to poly_pk.
   *  - x24 points to x2[1]. */

  addi x4, x0, 3
  beq  x21, x4, _handle_k3_compute_v
  addi x4, x0, 2
  beq  x21, x4, _handle_k2_compute_v

_handle_k4_compute_v:
  /* Generate x2[i]. */
  addi x10, x22, 0 /* ETA1 */
  addi x11, x24, 0 /* x2[i] */
  jal  x1, poly_getnoise_eta_1

  /* Prepare for generating x2[i + 1]. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, poly_getnoise_eta_init

  /* Unpack pk[i]. */
  addi x10, x9, 0
  la   x11, poly_pk
  jal  x1, poly_frombytes
  addi x9, x10, 0 /* Save address of pk to be unpacked later. */

  /* Compute x2[i] = ntt(x2[i]). */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  add        x10, x24, 0 /* x2[i] */
  la         x11, twiddles_ntt
  add        x12, x10, 0
  jal        x1, ntt

  /* Compute v += pk * x2[i]. */
  la      x10, poly_pk
  addi    x11, x24, 0 /* x2[i] */
  la      x12, twiddles_basemul
  la      x13, mpoly_v
  jal     x1, basemul_acc
  addi    x24, x11, 0 /* Point to mpolyvec_sp[i + 1]. */
  bn.wsrw mod, w16 /* mod = R | Q */

_handle_k3_compute_v:
  /* Generate x2[i]. */
  addi x10, x22, 0 /* ETA1 */
  addi x11, x24, 0 /* x2[i] */
  jal  x1, poly_getnoise_eta_1

  /* Prepare for generating x2[i + 1]. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, poly_getnoise_eta_init

  /* Unpack pk[i]. */
  addi x10, x9, 0
  la   x11, poly_pk
  jal  x1, poly_frombytes
  addi x9, x10, 0 /* Save address of pk to be unpacked later. */

  /* Compute x2[i] = ntt(x2[i]). */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  add        x10, x24, 0 /* x2[i] */
  la         x11, twiddles_ntt
  add        x12, x10, 0
  jal       x1, ntt

  /* Compute v += pk * x2[i]. */
  la      x10, poly_pk
  addi    x11, x24, 0 /* x2[i] */
  la      x12, twiddles_basemul
  la      x13, mpoly_v
  jal     x1, basemul_acc
  addi    x24, x11, 0 /* Point to mpolyvec_sp[i + 1]. */
  bn.wsrw mod, w16 /* mod = R | Q */

_handle_k2_compute_v:
  /* Generate x2[k - 1]. */
  addi x10, x22, 0 /* ETA1 */
  addi x11, x24, 0 /* x2[k - 1] */
  jal  x1, poly_getnoise_eta_1

  /* Prepare for initial `poly_getnoise_eta_2` call: generate epp. */
  addi x10, x18, 0 /* coins */
  slli x5, x21, 1 /* 2 * k */
  la   x11, nonce
  sw   x5, 0(x11)
  jal  x1, poly_getnoise_eta_init

  /* Compute x2[k - 1] = ntt(x2[k - 1]). */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  add        x10, x24, 0 /* x2[k - 1] */
  la         x11, twiddles_ntt
  add        x12, x10, 0 /* Output inplace. */
  jal        x1, ntt

  /* Unpack pk[k - 1]. */
  addi x10, x9, 0
  la   x11, poly_pk
  jal  x1, poly_frombytes
  addi x9, x10, 0 /* seed */

  /* Compute v += pk * x2[k - 1]. */
  la   x10, poly_pk
  addi x11, x24, 0 /* x2[k - 1] */
  la   x12, twiddles_basemul
  la   x13, mpoly_v
  jal  x1, basemul_acc

  /* Compute v = intt(v). */
  la      x10, mpoly_v
  la      x11, twiddles_intt
  addi    x12, x10, 0
  jal     x1, intt
  bn.wsrw mod, w16 /* Restore mod = R | Q */

  /* Compute v += k. */
  la   x10, mpoly_v
  la   x11, mpoly_k
  addi x12, x10, 0
  jal  x1, poly_add

  /* Generate epp. */
  la   x11, mpoly_epp
  jal  x1, poly_getnoise_eta_2

  /* Prepare for initial `poly_getnoise_eta_2` call: generate ep. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  sw   x21, 0(x11)
  jal  x1, poly_getnoise_eta_init

  /* Compute v += epp. */
  la   x10, mpoly_v
  la   x11, mpoly_epp
  addi x12, x10, 0
  jal  x1, poly_add

  /* Generate ep[0]. */
  la   x11, mpoly_ep
  jal  x1, poly_getnoise_eta_2

  /* Prepare for generating at[0][0]. */
  addi   x10, x9, 0 /* seed */
  la     x11, seed_ij
  bn.xor w0, w0, w0
  bn.sid x0, 0(x11)
  jal    x1, poly_gen_matrix_init

  /* Compress v. */
  la   x10, mpoly_v
  addi x11, x25, 0 /* ptr_packed_ct */
  addi x12, x21, 0 /* k */
  jal  x1, poly_compress

  /* Compare v and ct[k * POLY_POLYVECDECOMPRESSED_BYTES]. Output to r. */
  addi x5, x25, 0
  addi x6, x19, 0 /* ct */
  loop x21, 1
    add x6, x6, x27
  endloop
  addi x4, x0, 1
  srli x7, x26, 5

  bn.subi w2, w31, 1
  bn.mov  w4, w31
  loop x7, 5
    bn.lid x0, 0(x5++)
    bn.lid x4, 0(x6++)
    bn.cmp w0, w1
    bn.sel w3, w31, w2, FG0.Z
    bn.or  w4, w4, w3
  endloop
  /* First write to ptr_r; the later compares read-modify-write it. */
  addi   x4, x0, 4
  bn.sid x4, 0(x2) /* ptr_r */
  /**************************************************************************/


  /* The following block will:
   *  (1) sample at.row[i],
   *  (2) compute b = at.row[i] * x2[i],
   *  (3) compute b = intt(b),
   *  (4) sample ep[i]
   *  (5) compute b += ep[i]
   *  (6) compare b and ct, output to r. */
  /**************************************************************************/

  /* At this point:
   *  - x8 is free.
   *  - x9 points to seed (for matrix generation).
   *  - x18 points to coins (for cbd).
   *  - x19 points to ct (for unpacking).
   *  - x20 = nshares.
   *  - x21 is the security level k.
   *  - x22 is free.
   *  - x23 is free.
   *  - x24 is free. */

  addi x4, x0, 2
  beq  x21, x4, _handle_k2_compute_b

_handle_kn2_compute_b:

  addi x8, x21, -1 /* k - 1 */
  addi x21, x21, -2 /* k - 2 */
  slli x23, x8, 8 /* (k - 1) * 0x0100 */
  addi x23, x23, -1

  loop x8, 113
    /* Generate at[i][0]. */
    la   x11, poly_at
    jal  x1, poly_gen_matrix

    /* Prepare for generating at[i][1]. */
    addi x10, x9, 0 /* seed */
    la   x11, seed_ij
    lw   x4, 0(x11)
    addi x4, x4, 0x0100
    sw   x4, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute b = at[i][0] * x2[0]. */
    bn.wsrr    w16, mod /* mod = R | Q */
    bn.shv.16h w0, w16 << 1 /* w16 = 2*R | 2*Q */
    bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
    la         x10, poly_at
    la         x11, mpolyvec_sp
    la         x12, twiddles_basemul
    la         x13, mpoly_b
    jal        x1, basemul
    addi       x24, x11, 0 /* x2[1] */
    bn.wsrw    mod, w16 /* Restore mod = R | Q. */

    loop x21, 23
      /* Generate at[i][1]. */
      la   x11, poly_at
      jal  x1, poly_gen_matrix

      /* Prepare for generating at[i][2]. */
      addi x10, x9, 0 /* seed */
      la   x11, seed_ij
      lw   x4, 0(x11)
      addi x4, x4, 0x0100
      sw   x4, 0(x11)
      jal  x1, poly_gen_matrix_init

      /* Compute b += at[i][1] * x2[1]. */
      bn.wsrr    w16, mod /* mod = R | Q */
      bn.shv.16h w0, w16 << 1 /* w16 = 2*R | 2*Q */
      bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
      la         x10, poly_at
      addi       x11, x24, 0 /* x2[j] */
      la         x12, twiddles_basemul
      la         x13, mpoly_b
      jal        x1, basemul_acc
      addi       x24, x11, 0 /* x2[j + 1] */
      bn.wsrw    mod, w16 /* Restore mod = R | Q. */
    endloop

    /* Generate at[i][k - 1]. */
    la   x11, poly_at
    jal  x1, poly_gen_matrix

    /* Compute b += at[i][k - 1] * x2[k - 1]. */
    bn.wsrr    w16, mod /* mod = R | Q */
    bn.shv.16h w0, w16 << 1 /* w16 = 2*R | 2*Q */
    bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
    la         x10, poly_at
    addi       x11, x24, 0 /* x2[k - 1] */
    la         x12, twiddles_basemul
    la         x13, mpoly_b
    jal        x1, basemul_acc

    /* Compute b = intt(b). */
    la      x10, mpoly_b
    la      x11, twiddles_intt
    addi    x12, x10, 0
    jal     x1, intt
    bn.wsrw mod, w16 /* Restore mod = R | Q. */

    /* Prepare for generating ep[i + 1]. */
    addi x10, x18, 0 /* coins */
    la   x11, nonce
    lw   x5, 0(x11)
    addi x5, x5, 1
    sw   x5, 0(x11)
    jal  x1, poly_getnoise_eta_init

    /* Compute b += ep. */
    la   x10, mpoly_b
    la   x11, mpoly_ep
    addi x12, x10, 0
    jal  x1, poly_add

    /* Generate ep[i + 1]. */
    la   x11, mpoly_ep
    jal  x1, poly_getnoise_eta_2

    /* Prepare for generating at[i + 1][0]. */
    addi x10, x9, 0 /* seed */
    la   x11, seed_ij
    lw   x5, 0(x11)
    sub  x5, x5, x23
    sw   x5, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compress b. */
    la   x10, mpoly_b
    addi x11, x25, 0
    addi x12, x21, 2 /* k */
    jal  x1, poly_polyvec_compress

    /* Compare b and ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES].
     * Accumulate output to r. */
    addi x5, x25, 0
    addi x6, x19, 0 /* ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES] */
    srli x7, x27, 5
    addi x4, x0, 1

    bn.subi w2, w31, 1
    bn.mov  w4, w31
    loop x7, 5
      bn.lid x0, 0(x5++)
      bn.lid x4, 0(x6++)
      bn.cmp w0, w1
      bn.sel w3, w31, w2, FG0.Z
      bn.or  w4, w4, w3
    endloop
    bn.lid x0, 0(x2)
    bn.or  w0, w0, w4
    bn.sid x0, 0(x2) /* ptr_r */
    add    x19, x19, x27 /* ct[(i + 1) * POLY_POLYVECDECOMPRESSED_BYTES : (i + 2) * POLY_POLYVECDECOMPRESSED_BYTES]  */
  endloop

  /* Generate at[k - 1][0]. */
  la   x11, poly_at
  jal  x1, poly_gen_matrix

  /* Prepare for generating at[k - 1][1]. */
  addi x10, x9, 0 /* seed */
  la   x11, seed_ij
  lw   x4, 0(x11)
  addi x4, x4, 0x0100
  sw   x4, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compute b = at[k - 1][0] * x2[0]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x10, poly_at
  la         x11, mpolyvec_sp
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  jal        x1, basemul
  addi       x24, x11, 0 /* x2[1] */
  bn.wsrw    mod, w16 /* Restore mod = R | Q. */

  loop x21, 23
    /* Generate at[i][j]. */
    la   x11, poly_at
    jal  x1, poly_gen_matrix

    /* Prepare for generating at[i][j]. */
    addi x10, x9, 0 /* seed */
    la   x11, seed_ij
    lw   x4, 0(x11)
    addi x4, x4, 0x0100
    sw   x4, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute b += at[i][j] * x2[j]. */
    bn.wsrr    w16, mod /* mod = R | Q */
    bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
    bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
    la         x10, poly_at
    addi       x11, x24, 0 /* x2[j] */
    la         x12, twiddles_basemul
    la         x13, mpoly_b
    jal        x1, basemul_acc
    addi       x24, x11, 0 /* x2[j + 1] */
    bn.wsrw    mod, w16 /* Restore mod = R | Q. */
  endloop

  /* Generate at[k - 1][k - 1]. */
  la   x11, poly_at
  jal  x1, poly_gen_matrix

  /* Compute b += at[k - 1][k - 1] * x2[k - 1]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x10, poly_at
  addi       x11, x24, 0 /* x2[k - 1] */
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  jal        x1, basemul_acc

  /* Compute b = intt(b). */
  la      x10, mpoly_b
  la      x11, twiddles_intt
  addi    x12, x10, 0
  jal     x1, intt
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Compute b += ep. */
  la   x10, mpoly_b
  la   x11, mpoly_ep
  addi x12, x10, 0
  jal  x1, poly_add

  /* Compress b. */
  la   x10, mpoly_b
  addi x11, x25, 0
  addi x12, x21, 2 /* k */
  jal  x1, poly_polyvec_compress

  /* Compare b and ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES].
   * Accumulate output to r. */
  addi x5, x25, 0
  addi x6, x19, 0 /* ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES] */
  srli x7, x27, 5
  addi x4, x0, 1

  bn.subi w2, w31, 1
  bn.mov  w4, w31
  loop x7, 5
    bn.lid x0, 0(x5++)
    bn.lid x4, 0(x6++)
    bn.cmp w0, w1
    bn.sel w3, w31, w2, FG0.Z
    bn.or  w4, w4, w3
  endloop
  bn.lid x0, 0(x2)
  bn.or  w0, w0, w4 /* w0 is the comparison result. */
  /**************************************************************************/
  /* Restore x2 and x3. */
  addi x2, x3, 0
  lw   x3, 0(x2)
  addi x2, x2, 32
  ret

_handle_k2_compute_b:
  /* Generate at[0][0]. */
  la  x11, poly_at
  jal x1, poly_gen_matrix

  /* Prepare for generating at[0][1]. */
  addi x10, x9, 0 /* seed */
  la   x11, seed_ij
  lw   x4, 0(x11)
  addi x4, x4, 0x0100
  sw   x4, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compute b = at[0][0] * x2[0]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x10, poly_at
  la         x11, mpolyvec_sp
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  jal        x1, basemul
  addi       x24, x11, 0 /* x2[1] */
  bn.wsrw    mod, w16 /* Restore mod = R | Q. */

  /* Generate at[0][1]. */
  la  x11, poly_at
  jal x1, poly_gen_matrix

  /* Compute b += at[0][1] * x2[1]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x10, poly_at
  addi       x11, x24, 0 /* x2[1] */
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  jal        x1, basemul_acc

  /* Compute b = intt(b). */
  la      x10, mpoly_b
  la      x11, twiddles_intt
  addi    x12, x10, 0
  jal     x1, intt
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Prepare for generating ep[1]. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, poly_getnoise_eta_init

  /* Compute b += ep. */
  la   x10, mpoly_b
  la   x11, mpoly_ep
  addi x12, x10, 0
  jal  x1, poly_add

  /* Generate ep[1]. */
  la   x11, mpoly_ep
  jal  x1, poly_getnoise_eta_2

  /* Prepare for generating at[1][0]. */
  addi x10, x9, 0 /* seed */
  la   x11, seed_ij
  addi x5, x0, 1
  sw   x5, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compress b. */
  la   x10, mpoly_b
  addi x11, x25, 0
  addi x12, x21, 0 /* k */
  jal  x1, poly_polyvec_compress

  /* Compare b and ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES].
   * Accumulate output to r. */
  addi x5, x25, 0
  addi x6, x19, 0 /* ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES] */
  srli x7, x27, 5
  addi x4, x0, 1

  bn.subi w2, w31, 1
  bn.mov  w4, w31
  loop x7, 5
    bn.lid x0, 0(x5++)
    bn.lid x4, 0(x6++)
    bn.cmp w0, w1
    bn.sel w3, w31, w2, FG0.Z
    bn.or  w4, w4, w3
  endloop
  bn.lid x0, 0(x2)
  bn.or  w0, w0, w4
  bn.sid x0, 0(x2) /* ptr_r */

  /* Generate at[1][0]. */
  la  x11, poly_at
  jal x1, poly_gen_matrix

  /* Prepare for generating at[1][1]. */
  addi x10, x9, 0 /* seed */
  la   x11, seed_ij
  lw   x4, 0(x11)
  addi x4, x4, 0x0100
  sw   x4, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compute b = at[1][0] * x2[0]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x10, poly_at
  la         x11, mpolyvec_sp
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  jal        x1, basemul
  addi       x24, x11, 0 /* x2[1] */
  bn.wsrw    mod, w16 /* Restore mod = R | Q. */

  /* Generate at[1][1]. */
  la  x11, poly_at
  jal x1, poly_gen_matrix

  /* Compute b += at[1][1] * x2[1]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x10, poly_at
  addi       x11, x24, 0 /* x2[1] */
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  jal        x1, basemul_acc

  /* Compute b = intt(b). */
  la      x10, mpoly_b
  la      x11, twiddles_intt
  addi    x12, x10, 0
  jal     x1, intt
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Compute b += ep. */
  la   x10, mpoly_b
  la   x11, mpoly_ep
  addi x12, x10, 0
  jal  x1, poly_add

  /* Compress b. */
  la   x10, mpoly_b
  addi x11, x25, 0
  addi x12, x21, 0 /* k */
  jal  x1, poly_polyvec_compress

  /* Compare b and ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES].
   * Accumulate output to r. */
  addi x5, x25, 0
  addi x6, x19, 320 /* ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES] */
  srli x7, x27, 5
  addi x4, x0, 1

  bn.subi w2, w31, 1
  bn.mov  w4, w31
  loop x7, 5
    bn.lid x0, 0(x5++)
    bn.lid x4, 0(x6++)
    bn.cmp w0, w1
    bn.sel w3, w31, w2, FG0.Z
    bn.or  w4, w4, w3
  endloop
  bn.lid x0, 0(x2)
  bn.or  w0, w0, w4 /* w0 is the comparison result. */
  /**************************************************************************/
  /* Restore x2 and x3. */
  addi x2, x3, 0
  lw   x3, 0(x2)
  addi x2, x2, 32
  ret

#else
  addi x4, x0, 4
  beq  x21, x4, _compute_k4_consts
_compute_kn4_consts:
  addi x26, x0, 128 /* dv * 32 = 4 * 32 */
  addi x27, x0, 320 /* du * 32 = 10 * 32 */
  beq  x0, x0, _continue
_compute_k4_consts:
  addi x26, x0, 160 /* dv * 32 = 5 * 32 */
  addi x27, x0, 352 /* du * 32 = 11 * 32 */
_continue:
  /* Adjust stack for comparison result r. */
  slli x5, x20, 5 /* nshares * 32 */
  sub  x2, x2, x5

  /* The first share of r is (1 << N) - 1. The other shares are 0. */
  addi    x5, x2, 0 /* r */
  bn.xor  w0, w0, w0
  bn.subi w0, w0, 1
  bn.sid  x0, 0(x5++)
  bn.xor  w0, w0, w0
  addi    x6, x20, -1 /* nshares - 1 */
  loop x6, 1
    bn.sid x0, 0(x5++)
  endloop

  /* Compute k = onebitdecompress(m). */
  bn.wsrr w16, mod /* mod = R | Q */
  /* x10 is already ptr_m. */
  la   x12, mpoly_k
  jal  x1, onebitdecompress

  /* The following block will:
   *  (1) unpack pk[i],
   *  (2) sample x2[i],
   *  (3) compute x2[i] = ntt(x2[i]),
   *  (4) compute v += pk[i] * x2[i],
   *  (5) compute v = intt(v),
   *  (6) compute v += k
   *  (7) sample epp
   *  (8) compute v += epp
   *  (9) compare v and ct, output to r. */
  /**************************************************************************/
  addi x4, x0, 2
  beq  x21, x4, _handle_k2_eta_1
_handle_kn2_eta_1:
  addi x22, x0, 2 /* ETA1 */
  beq  x0, x0, _continue_compute_v
_handle_k2_eta_1:
  addi x22, x0, 3 /* ETA1 */

_continue_compute_v:

  /* Prepare for initial `poly_getnoise_eta_1` call: generate x2. */
  addi   x10, x18, 0 /* coins */
  la     x11, nonce
  bn.xor w0, w0, w0
  bn.sid x0, 0(x11)
  jal    x1, masked_poly_getnoise_eta_init

  /* Unpack pk[0]. */
  addi x10, x9, 0
  la   x11, poly_pk
  jal  x1, poly_frombytes
  addi x9, x10, 0 /* Save address of pk to be unpacked later. */

  /* Generate x2[0]. */
  addi x10, x22, 0 /* eta = ETA1 */
  la   x11, mpolyvec_sp
  jal  x1, masked_poly_getnoise_eta_1

  /* Prepare for generating x2[1]. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, masked_poly_getnoise_eta_init

  /* Compute x2[0] = ntt(x2[0]). */
  bn.wsrr    w16, mod /* w16 = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x10, mpolyvec_sp
  la         x11, twiddles_ntt
  add        x12, x10, 0
  loop x20, 3
    jal x1, whitening
    jal x1, ntt
    nop
  endloop

  /* Compute v = pk[0] * x2[0]. */
  la   x8, poly_pk
  addi x10, x8, 0
  la   x11, mpolyvec_sp
  la   x12, twiddles_basemul
  la   x13, mpoly_v
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul
    addi x10, x8, 0
  endloop

  addi    x24, x11, 0 /* Point to x2[1]. */
  bn.wsrw mod, w16 /* Reset mod = R | Q */

  /* At this point:
   *  - x9 points to packed pk.
   *  - x18 points to coins (for cbd).
   *  - x19 points to ct (for later).
   *  - x20 = nshares.
   *  - x21 is the security level k.
   *  - x22 is ETA1.
   *  - x23 points to poly_pk.
   *  - x24 points to x2[1]. */

  addi x4, x0, 3
  beq  x21, x4, _handle_k3_compute_v
  addi x4, x0, 2
  beq  x21, x4, _handle_k2_compute_v

_handle_k4_compute_v:
  /* Generate x2[i]. */
  addi x10, x22, 0 /* eta = ETA1 */
  addi x11, x24, 0 /* x2[i] */
  jal  x1, masked_poly_getnoise_eta_1

  /* Prepare for generating x2[i + 1]. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, masked_poly_getnoise_eta_init

  /* Unpack pk[i]. */
  addi x10, x9, 0
  la   x11, poly_pk
  jal  x1, poly_frombytes
  addi x9, x10, 0 /* Save address of pk to be unpacked later. */

  /* Compute x2[i] = ntt(x2[i]). */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  add        x10, x24, 0 /* x2[i] */
  la         x11, twiddles_ntt
  add        x12, x10, 0
  loop x20, 3
    jal x1, whitening
    jal x1, ntt
    nop
  endloop

  /* Compute v += pk * x2[i]. */
  la   x8, poly_pk
  addi x10, x8, 0
  addi x11, x24, 0 /* x2[i] */
  la   x12, twiddles_basemul
  la   x13, mpoly_v
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul_acc
    addi x10, x8, 0
  endloop
  addi    x24, x11, 0 /* Point to mpolyvec_sp[i + 1]. */
  bn.wsrw mod, w16 /* mod = R | Q */

_handle_k3_compute_v:
  /* Generate x2[i]. */
  addi x10, x22, 0 /* eta = ETA1 */
  addi x11, x24, 0 /* x2[i] */
  jal  x1, masked_poly_getnoise_eta_1

  /* Prepare for generating x2[i + 1]. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, masked_poly_getnoise_eta_init

  /* Unpack pk[i]. */
  addi x10, x9, 0
  la   x11, poly_pk
  jal  x1, poly_frombytes
  addi x9, x10, 0 /* Save address of pk to be unpacked later. */

  /* Compute x2[i] = ntt(x2[i]). */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  add        x10, x24, 0 /* x2[i] */
  la         x11, twiddles_ntt
  add        x12, x10, 0
  loop x20, 3
    jal x1, whitening
    jal x1, ntt
    nop
  endloop

  /* Compute v += pk * x2[i]. */
  la   x8, poly_pk
  addi x10, x8, 0
  addi x11, x24, 0 /* x2[i] */
  la   x12, twiddles_basemul
  la   x13, mpoly_v
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul_acc
    addi x10, x8, 0
  endloop
  addi    x24, x11, 0 /* Point to mpolyvec_sp[i + 1]. */
  bn.wsrw mod, w16 /* mod = R | Q */

_handle_k2_compute_v:
  /* Generate x2[k - 1]. */
  addi x10, x22, 0 /* eta = ETA1 */
  addi x11, x24, 0 /* x2[k - 1] */
  jal  x1, masked_poly_getnoise_eta_1

  /* Prepare for initial `poly_getnoise_eta_2` call: generate epp. */
  addi x10, x18, 0 /* coins */
  slli x5, x21, 1 /* 2 * k */
  la   x11, nonce
  sw   x5, 0(x11)
  jal  x1, masked_poly_getnoise_eta_init

  /* Compute x2[k - 1] = ntt(x2[k - 1]). */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  add        x10, x24, 0 /* x2[k - 1] */
  la         x11, twiddles_ntt
  add        x12, x10, 0 /* Output inplace. */
  loop x20, 3
    jal  x1, whitening
    jal  x1, ntt
    nop
  endloop

  /* Unpack pk[k - 1]. */
  addi x10, x9, 0
  la   x11, poly_pk
  jal  x1, poly_frombytes
  addi x9, x10, 0 /* seed */

  /* Compute v += pk * x2[k - 1]. */
  la   x8, poly_pk
  addi x10, x8, 0
  addi x11, x24, 0 /* x2[k - 1] */
  la   x12, twiddles_basemul
  la   x13, mpoly_v
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul_acc
    addi x10, x8, 0
  endloop

  /* Compute v = intt(v). */
  la   x10, mpoly_v
  la   x11, twiddles_intt
  addi x12, x10, 0
  loop x20, 3
    jal x1, whitening
    jal x1, intt
    nop
  endloop
  bn.wsrw mod, w16 /* Restore mod = R | Q */

  /* Compute v += k. */
  la   x10, mpoly_v
  la   x11, mpoly_k
  addi x12, x10, 0
  loop x20, 4
    /* Whitening. */
    bn.xor w0, w0, w0
    bn.xor w1, w1, w1
    jal    x1, poly_add
    nop
  endloop

  /* Generate epp. */
  addi x10, x0, 2 /* eta = ETA2 = 2 */
  la   x11, mpoly_epp
  jal  x1, masked_poly_getnoise_eta_2

  /* Prepare for initial `poly_getnoise_eta_2` call: generate ep. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  sw   x21, 0(x11)
  jal  x1, masked_poly_getnoise_eta_init

  /* Compute v += epp. */
  la   x10, mpoly_v
  la   x11, mpoly_epp
  addi x12, x10, 0
  loop x20, 4
    /* Whitening. */
    bn.xor w0, w0, w0
    bn.xor w1, w1, w1
    jal    x1, poly_add
    nop
  endloop

  /* Generate ep[0]. */
  addi x10, x0, 2 /* eta = ETA2 = 2 */
  la   x11, mpoly_ep
  jal  x1, masked_poly_getnoise_eta_2

  /* Prepare for generating at[0][0]. */
  addi   x10, x9, 0 /* seed */
  la     x11, seed_ij
  bn.xor w0, w0, w0
  bn.sid x0, 0(x11)
  jal    x1, poly_gen_matrix_init

  /* Compare v and ct[k * POLY_POLYVECDECOMPRESSED_BYTES]. Output to r. */
  la   x10, mpoly_v
  addi x11, x19, 0 /* ct */
  loop x21, 1
    add x11, x11, x27
  endloop
  addi x12, x26, 0 /* dv * 32 */
  addi x14, x2, 0 /* r */
  addi x15, x21, 0 /* k */
  jal  x1, poly_masked_compare_dv
  /**************************************************************************/


  /* The following block will:
   *  (1) sample at.row[i],
   *  (2) compute b = at.row[i] * x2[i],
   *  (3) compute b = intt(b),
   *  (4) sample ep[i]
   *  (5) compute b += ep[i]
   *  (6) compare b and ct, output to r. */
  /**************************************************************************/

  /* At this point:
   *  - x8 is free.
   *  - x9 points to seed (for matrix generation).
   *  - x18 points to coins (for cbd).
   *  - x19 points to ct (for unpacking).
   *  - x20 = nshares.
   *  - x21 is the security level k.
   *  - x22 is free.
   *  - x23 is free.
   *  - x24 is free. */

  addi x4, x0, 2
  beq  x21, x4, _handle_k2_compute_b

_handle_kn2_compute_b:

  addi x8, x21, -1 /* k - 1 */
  addi x21, x21, -2 /* k - 2 */
  slli x23, x8, 8 /* (k - 1) * 0x0100 */
  addi x23, x23, -1

  loop x8, 120
    /* Generate at[i][0]. */
    la   x11, poly_at
    jal  x1, poly_gen_matrix

    /* Prepare for generating at[i][1]. */
    addi x10, x9, 0 /* seed */
    la   x11, seed_ij
    lw   x4, 0(x11)
    addi x4, x4, 0x0100
    sw   x4, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute b = at[i][0] * x2[0]. */
    bn.wsrr    w16, mod /* mod = R | Q */
    bn.shv.16h w0, w16 << 1 /* w16 = 2*R | 2*Q */
    bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
    la         x22, poly_at
    addi       x10, x22, 0
    la         x11, mpolyvec_sp
    la         x12, twiddles_basemul
    la         x13, mpoly_b
    loop x20, 3
      jal  x1, whitening
      jal  x1, basemul
      addi x10, x22, 0
    endloop
    addi    x24, x11, 0 /* x2[1] */
    bn.wsrw mod, w16 /* Restore mod = R | Q. */

    loop x21, 27
      /* Generate at[i][1]. */
      la   x11, poly_at
      jal  x1, poly_gen_matrix

      /* Prepare for generating at[i][2]. */
      addi x10, x9, 0 /* seed */
      la   x11, seed_ij
      lw   x4, 0(x11)
      addi x4, x4, 0x0100
      sw   x4, 0(x11)
      jal  x1, poly_gen_matrix_init

      /* Compute b += at[i][1] * x2[1]. */
      bn.wsrr    w16, mod /* mod = R | Q */
      bn.shv.16h w0, w16 << 1 /* w16 = 2*R | 2*Q */
      bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
      la         x22, poly_at
      addi       x10, x22, 0
      addi       x11, x24, 0 /* x2[j] */
      la         x12, twiddles_basemul
      la         x13, mpoly_b
      loop x20, 3
        jal  x1, whitening
        jal  x1, basemul_acc
        addi x10, x22, 0 /* poly_at */
      endloop
      addi    x24, x11, 0 /* x2[j + 1] */
      bn.wsrw mod, w16 /* Restore mod = R | Q. */
    endloop

    /* Generate at[i][k - 1]. */
    la   x11, poly_at
    jal  x1, poly_gen_matrix

    /* Compute b += at[i][k - 1] * x2[k - 1]. */
    bn.wsrr    w16, mod /* mod = R | Q */
    bn.shv.16h w0, w16 << 1 /* w16 = 2*R | 2*Q */
    bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
    la         x22, poly_at
    addi       x10, x22, 0
    addi       x11, x24, 0 /* x2[k - 1] */
    la         x12, twiddles_basemul
    la         x13, mpoly_b
    loop x20, 3
      jal  x1, whitening
      jal  x1, basemul_acc
      addi x10, x22, 0 /* poly_at */
    endloop

    /* Compute b = intt(b). */
    la   x10, mpoly_b
    la   x11, twiddles_intt
    addi x12, x10, 0
    loop x20, 3
      jal x1, whitening
      jal x1, intt
      nop
    endloop
    bn.wsrw mod, w16 /* Restore mod = R | Q. */

    /* Prepare for generating ep[i + 1]. */
    addi x10, x18, 0 /* coins */
    la   x11, nonce
    lw   x5, 0(x11)
    addi x5, x5, 1
    sw   x5, 0(x11)
    jal  x1, masked_poly_getnoise_eta_init

    /* Compute b += ep. */
    la   x10, mpoly_b
    la   x11, mpoly_ep
    addi x12, x10, 0
    loop x20, 4
      /* Whitening. */
      bn.xor w0, w0, w0
      bn.xor w1, w1, w1
      jal    x1, poly_add
      nop
    endloop

    /* Generate ep[i + 1]. */
    addi x10, x0, 2 /* eta = ETA2 = 2 */
    la   x11, mpoly_ep
    jal  x1, masked_poly_getnoise_eta_2

    /* Prepare for generating at[i + 1][0]. */
    addi x10, x9, 0 /* seed */
    la   x11, seed_ij
    lw   x5, 0(x11)
    sub  x5, x5, x23
    sw   x5, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compare b and ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES].
     * Accumulate output to r. */
    la   x10, mpoly_b
    addi x11, x19, 0 /* ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES] */
    addi x12, x27, 0
    addi x14, x2, 0 /* r */
    addi x15, x21, 2 /* k */
    jal  x1, poly_masked_compare_du
    add  x19, x19, x27 /* ct[(i + 1) * POLY_POLYVECDECOMPRESSED_BYTES : (i + 2) * POLY_POLYVECDECOMPRESSED_BYTES]  */
  endloop

  /* Generate at[k - 1][0]. */
  la   x11, poly_at
  jal  x1, poly_gen_matrix

  /* Prepare for generating at[k - 1][1]. */
  addi x10, x9, 0 /* seed */
  la   x11, seed_ij
  lw   x4, 0(x11)
  addi x4, x4, 0x0100
  sw   x4, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compute b = at[k - 1][0] * x2[0]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x22, poly_at
  addi       x10, x22, 0
  la         x11, mpolyvec_sp
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul
    addi x10, x22, 0 /* poly_at */
  endloop
  addi    x24, x11, 0 /* x2[1] */
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  loop x21, 27
    /* Generate at[i][j]. */
    la   x11, poly_at
    jal  x1, poly_gen_matrix

    /* Prepare for generating at[i][j]. */
    addi x10, x9, 0 /* seed */
    la   x11, seed_ij
    lw   x4, 0(x11)
    addi x4, x4, 0x0100
    sw   x4, 0(x11)
    jal  x1, poly_gen_matrix_init

    /* Compute b += at[i][j] * x2[j]. */
    bn.wsrr    w16, mod /* mod = R | Q */
    bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
    bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
    la         x22, poly_at
    addi       x10, x22, 0
    addi       x11, x24, 0 /* x2[j] */
    la         x12, twiddles_basemul
    la         x13, mpoly_b
    loop x20, 3
      jal  x1, whitening
      jal  x1, basemul_acc
      addi x10, x22, 0
    endloop
    addi    x24, x11, 0 /* x2[j + 1] */
    bn.wsrw mod, w16 /* Restore mod = R | Q. */
  endloop

  /* Generate at[k - 1][k - 1]. */
  la   x11, poly_at
  jal  x1, poly_gen_matrix

  /* Compute b += at[k - 1][k - 1] * x2[k - 1]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x22, poly_at
  addi       x10, x22, 0 /* poly_at */
  addi       x11, x24, 0 /* x2[k - 1] */
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul_acc
    addi x10, x22, 0 /* poly_at */
  endloop

  /* Compute b = intt(b). */
  la   x10, mpoly_b
  la   x11, twiddles_intt
  addi x12, x10, 0
  loop x20, 3
    jal x1, whitening
    jal x1, intt
    nop
  endloop
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Compute b += ep. */
  la   x10, mpoly_b
  la   x11, mpoly_ep
  addi x12, x10, 0
  loop x20, 4
    /* Whitening. */
    bn.xor w0, w0, w0
    bn.xor w1, w1, w1
    jal    x1, poly_add
    nop
  endloop

  /* Compare b and ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES].
   * Accumulate output to r. */
  la   x10, mpoly_b
  addi x11, x19, 0 /* ct[(k - 1) * POLY_POLYVECDECOMPRESSED_BYTES : k * POLY_POLYVECDECOMPRESSED_BYTES]  */
  addi x12, x27, 0
  addi x14, x2, 0 /* r */
  addi x15, x21, 2 /* k */
  jal  x1, poly_masked_compare_du
  /**************************************************************************/
  beq  x0, x0, _finalize_compare

_handle_k2_compute_b:
  /* Generate at[0][0]. */
  la  x11, poly_at
  jal x1, poly_gen_matrix

  /* Prepare for generating at[0][1]. */
  addi x10, x9, 0 /* seed */
  la   x11, seed_ij
  lw   x4, 0(x11)
  addi x4, x4, 0x0100
  sw   x4, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compute b = at[0][0] * x2[0]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x22, poly_at
  addi       x10, x22, 0 /* poly_at */
  la         x11, mpolyvec_sp
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul
    addi x10, x22, 0 /* poly_at */
  endloop
  addi    x24, x11, 0 /* x2[1] */
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Generate at[0][1]. */
  la  x11, poly_at
  jal x1, poly_gen_matrix

  /* Compute b += at[0][1] * x2[1]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x22, poly_at
  addi       x10, x22, 0
  addi       x11, x24, 0 /* x2[1] */
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul_acc
    addi x10, x22, 0
  endloop

  /* Compute b = intt(b). */
  la   x10, mpoly_b
  la   x11, twiddles_intt
  addi x12, x10, 0
  loop x20, 3
    jal x1, whitening
    jal x1, intt
    nop
  endloop
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Prepare for generating ep[1]. */
  addi x10, x18, 0 /* coins */
  la   x11, nonce
  lw   x5, 0(x11)
  addi x5, x5, 1
  sw   x5, 0(x11)
  jal  x1, masked_poly_getnoise_eta_init

  /* Compute b += ep. */
  la   x10, mpoly_b
  la   x11, mpoly_ep
  addi x12, x10, 0
  loop x20, 4
    /* Whitening. */
    bn.xor w0, w0, w0
    bn.xor w1, w1, w1
    jal    x1, poly_add
    nop
  endloop

  /* Generate ep[1]. */
  addi x10, x0, 2 /* eta = ETA2 = 2 */
  la   x11, mpoly_ep
  jal  x1, masked_poly_getnoise_eta_2

  /* Prepare for generating at[1][0]. */
  addi x10, x9, 0 /* seed */
  la   x11, seed_ij
  addi x5, x0, 1
  sw   x5, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compare b and ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES].
   * Accumulate output to r. */
  la   x10, mpoly_b
  addi x11, x19, 0 /* ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES] */
  addi x12, x0, 320
  addi x14, x2, 0 /* r */
  addi x15, x21, 0 /* k */
  jal  x1, poly_masked_compare_du

  /* Generate at[1][0]. */
  la  x11, poly_at
  jal x1, poly_gen_matrix

  /* Prepare for generating at[1][1]. */
  addi x10, x9, 0 /* seed */
  la   x11, seed_ij
  lw   x4, 0(x11)
  addi x4, x4, 0x0100
  sw   x4, 0(x11)
  jal  x1, poly_gen_matrix_init

  /* Compute b = at[1][0] * x2[0]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x22, poly_at
  addi       x10, x22, 0
  la         x11, mpolyvec_sp
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul
    addi x10, x22, 0
  endloop
  addi    x24, x11, 0 /* x2[1] */
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Generate at[1][1]. */
  la  x11, poly_at
  jal x1, poly_gen_matrix

  /* Compute b += at[1][1] * x2[1]. */
  bn.wsrr    w16, mod /* mod = R | Q */
  bn.shv.16h w0, w16 << 1 /* w0 = 2*R | 2*Q */
  bn.wsrw    mod, w0 /* mod = 2*R | 2*Q */
  la         x22, poly_at
  addi       x10, x22, 0
  addi       x11, x24, 0 /* x2[1] */
  la         x12, twiddles_basemul
  la         x13, mpoly_b
  loop x20, 3
    jal  x1, whitening
    jal  x1, basemul_acc
    addi x10, x22, 0
  endloop

  /* Compute b = intt(b). */
  la   x10, mpoly_b
  la   x11, twiddles_intt
  addi x12, x10, 0
  loop x20, 3
    jal x1, whitening
    jal x1, intt
    nop
  endloop
  bn.wsrw mod, w16 /* Restore mod = R | Q. */

  /* Compute b += ep. */
  la   x10, mpoly_b
  la   x11, mpoly_ep
  addi x12, x10, 0
  loop x20, 4
    /* Whitening. */
    bn.xor w0, w0, w0
    bn.xor w1, w1, w1
    jal    x1, poly_add
    nop
  endloop

  /* Compare b and ct[i * POLY_POLYVECDECOMPRESSED_BYTES : (i + 1) * POLY_POLYVECDECOMPRESSED_BYTES].
   * Accumulate output to r. */
  la   x10, mpoly_b
  addi x11, x19, 320 /* ct[(k - 1) * POLY_POLYVECDECOMPRESSED_BYTES : k * POLY_POLYVECDECOMPRESSED_BYTES]  */
  addi x12, x0, 320
  addi x14, x2, 0 /* r */
  addi x15, x21, 0 /* k */
  jal  x1, poly_masked_compare_du
  /**************************************************************************/

_finalize_compare:

  /* Finalize the comparison result. */
  addi x10, x2, 0 /* r */
  addi x11, x20, 0 /* nshares */
  jal  x1, finalize_cmp

  /* Unmask comparison result. */
  addi   x10, x2, 0 /* r */
  bn.lid x0, 0(x10++)
  addi   x5, x20, -1 /* nshares - 1 */
  addi   x4, x0, 1
  loop x5, 2
    bn.lid x4, 0(x10++)
    bn.xor w0, w0, w1
  endloop

  /* Restore x2 and x3. */
  addi x2, x3, 0
  lw   x3, 0(x2)
  addi x2, x2, 32
  ret

#endif
