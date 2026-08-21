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

/* Config to start a SHA3_256 operation. */
#define SHA3_256_CFG 0x8

/**
 * Key generation for the CCA-secure ML-KEM key encapsulation mechanism.
 *
 * Run indcpa_keypair on the seed d, then complete the secret key by appending
 * the public key, its hash H(pk) and the implicit-rejection seed z.
 *
 * The seed buffer holds d || z, that is 2 * KYBER_SYMBYTES = 64 bytes. When
 * built with HARDENED, both halves are Boolean-shared into two shares each, so
 * the buffer holds d_0 || d_1 || z_0 || z_1 and is 128 bytes long instead.
 *
 * @param[in]  x10: dmem pointer to the input seed
 * @param[out] x11: dmem pointer to the output public key
 * @param[out] x12: dmem pointer to the output secret key
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

.globl crypto_kem_keypair
.type crypto_kem_keypair, @function
crypto_kem_keypair:
  /* Save addresses. */
  la x5, dptr_coins
  sw x10, 0(x5)
  la x5, dptr_pk
  sw x11, 0(x5)
  la x5, k
  sw x13, 0(x5)

#ifdef HARDENED
  /* Refresh the Boolean shares of seed d (coins + 0, coins + 32). */
  addi x8, x10, 0
  addi x9, x11, 0
  addi x18, x12, 0
  addi x11, x0, 1
  addi x12, x0, 32
  addi x14, x10, 0
  jal  x1, refreshios
  addi x10, x8, 0
  addi x11, x9, 0
  addi x12, x18, 0
#endif

  /*** indcpa_keypair ***/
  jal  x1, indcpa_keypair

  la   x5, k
  lw   x5, 0(x5)
  addi x4, x0, 2
  beq  x5, x4, _pk_len_k2
  addi x4, x0, 3
  beq  x5, x4, _pk_len_k3
  addi x8, x0, 1568
  beq  x0, x0, _continue
_pk_len_k3:
  addi x8, x0, 1184
  beq  x0, x0, _continue
_pk_len_k2:
  addi x8, x0, 800

_continue:
  /* Copy pk to sk and compute H(pk). */
  la      x5, dptr_pk
  lw      x10, 0(x5)
  slli    x5, x8, 5
  addi    x5, x5, SHA3_256_CFG
  csrrw   x0, kmac_cfg, x5

  la      x6, dptr_sk
  lw      x6, 0(x6)
  srli    x8, x8, 5
  loop x8, 3
    bn.lid  x0, 0(x10++)
    bn.sid  x0, 0(x6++)
    bn.wsrw kmac_msg, w0
  endloop
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x6++)

  /* Copy z to sk. */
  la     x5, dptr_coins
  lw     x5, 0(x5)
#ifdef HARDENED
  bn.lid x0, 64(x5)
  bn.sid x0, 0(x6)
  bn.xor w0, w0, w0 /* Whitening. */
  bn.lid x0, 96(x5)
  bn.sid x0, 32(x6)
#else
  bn.lid x0, 32(x5)
  bn.sid x0, 0(x6)
#endif
  ret
