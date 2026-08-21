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

/* Config to start a SHAKE-256 operation. */
#define SHAKE256_CFG 0xA
/* Config to start a SHA3_512 operation. */
#define SHA3_512_CFG 0x10

/**
 * Decapsulation for the CCA-secure ML-KEM key encapsulation mechanism.
 *
 * Derive the shared secret from a ciphertext and a secret key: decrypt the
 * ciphertext, re-encrypt the recovered message with indcpa_enc_cmp and compare
 * the result against the input ciphertext. If the comparison fails, the
 * implicit-rejection secret derived from z is returned instead of the true
 * shared secret; the two are selected with a constant-time conditional move.
 *
 * @param[in]  x10 (x10): dmem pointer to the input ciphertext
 * @param[in]  x11 (x11): dmem pointer to the input masked secret key, holding
 *                       NSHARES shares
 * @param[out] x12 (x12): dmem pointer to the output shared secret
 * @param[in]  x13 (x13): k, the security level
 * @param[in]  w31: all-zero register
 *
 * UNPROTECTED
 * clobbered registers: x2 to x15, x18 to x28, w0 to w26, w30, acc, acch, mod
 * clobbered flag groups: FG0
 *
 * HARDENED
 * clobbered registers: x2 to x31, w0 to w30, acc, acch, mod
 * clobbered flag groups: FG0
 */
.globl crypto_kem_dec
.type crypto_kem_dec, @function
crypto_kem_dec:
  addi x4, x0, 2
  beq  x13, x4, _save_k2_ptrs
  addi x4, x0, 3
  beq  x13, x4, _save_k3_ptrs

  /* Save input and output addresses. */
  /* Public ciphertext. */
  la x5, dptr_ct
  sw x10, 0(x5)
  /* Public key for PKE.Enc. */
  addi x6, x11, 0
  loopi NSHARES, 1
      addi x6, x6, 1536
  endloop
  la x5, dptr_pk
  sw x6, 0(x5)
  /* H(pk). */
  addi x6, x6, 1568
  la   x5, dptr_h
  sw   x6, 0(x5)
  /* Shared key. */
  la x5, dptr_ss
  sw x12, 0(x5)
  /* k. */
  la x5, k
  sw x13, 0(x5)
  /* Ciphertext bytes. */
  la   x5, ctbytes
  addi x6, x0, 1568
  sw   x6, 0(x5)

  beq  x0, x0, _continue

_save_k2_ptrs:
  /* Save input and output addresses. */
  /* Public ciphertext. */
  la x5, dptr_ct
  sw x10, 0(x5)
  /* Public key for PKE.Enc. */
  addi x6, x11, 0
  loopi NSHARES, 1
      addi x6, x6, 768
  endloop
  la x5, dptr_pk
  sw x6, 0(x5)
  /* H(pk). */
  addi x6, x6, 800
  la   x5, dptr_h
  sw   x6, 0(x5)
  /* Shared key. */
  la x5, dptr_ss
  sw x12, 0(x5)
  /* k. */
  la x5, k
  sw x13, 0(x5)
  /* Ciphertext bytes. */
  la   x5, ctbytes
  addi x6, x0, 768
  sw   x6, 0(x5)

  beq  x0, x0, _continue

_save_k3_ptrs:
  /* Save input and output addresses. */
  /* Public ciphertext. */
  la x5, dptr_ct
  sw x10, 0(x5)
  /* Public key for PKE.Enc. */
  addi x6, x11, 0
  loopi NSHARES, 1
      addi x6, x6, 1152
  endloop
  la x5, dptr_pk
  sw x6, 0(x5)
  /* H(pk). */
  addi x6, x6, 1184
  la   x5, dptr_h
  sw   x6, 0(x5)
  /* Shared key. */
  la x5, dptr_ss
  sw x12, 0(x5)
  /* k. */
  la x5, k
  sw x13, 0(x5)
  /* Ciphertext bytes. */
  la   x5, ctbytes
  addi x6, x0, 1088
  sw   x6, 0(x5)

_continue:

#ifdef HARDENED
  /* Refresh z's Boolean shares; clobbers x10/x11, so stash/reload sk/ct. */
  addi x8, x11, 0
  la   x10, dptr_h
  lw   x10, 0(x10)
  addi x10, x10, 32
  addi x11, x0, 1
  addi x12, x0, 32
  addi x14, x10, 0
  jal  x1, refreshios
  la   x5, dptr_ct
  lw   x10, 0(x5)
  addi x11, x8, 0
#endif

  /* m = indcpa_dec(ct, sk). */
  la  x12, m
  jal x1, indcpa_dec

#ifdef HARDENED
  /* Since the output message of indcpa_dec is in a special order due
   * to performance reason for masked_poly_tomsg gagdet, we reorder the
   * message m here before hashing it. Note that the re-ordered message is
   * put elsewhere, not in buffer for m again. Otherwise, the re-encryption
   * will fail since the masked one-bit decompression gadget takes into
   * account the special order of the message m. */
  la x5, m
  la x6, mtmp
  li x4, 3
  loopi 2, 11
    /* Whitening. */
    bn.xor w0, w0, w0
    bn.xor w1, w1, w1
    bn.xor w3, w3, w3
    bn.lid x0, 0(x5++)
    loopi 16, 5
      bn.shv.16h w1, w0 >> 15
      loopi 16, 2
        bn.rshi w3, w1, w3 >> 1
        bn.rshi w1, w31, w1 >> 16
      endloop
      bn.shv.16h w0, w0 << 1
    endloop
    bn.sid x4, 0(x6++)
  endloop

  /* Compute kr = hash_g(m || h). */
  la      x5, dptr_h
  lw      x5, 0(x5)
  addi    x4, x0, 1
  bn.lid  x4, 0(x5)
  /* Send the message to KMAC. */
  addi    x5, x0, 64
  slli    x5, x5, 5
  addi    x5, x5, SHA3_512_CFG
  addi    x6, x0, 1
  slli    x6, x6, 20
  add     x5, x5, x6
  csrrw   x0, kmac_cfg, x5
  /* Send m. */
  la      x6, mtmp
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.lid  x0, 0(x6++)
  bn.wsrw kmac_msg, w0 /* m[0] */
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.lid  x0, 0(x6)
  bn.wsrw kmac_msg1, w0 /* m[1] */
  /* Send h. */
  bn.wsrw kmac_msg, w1 /* h */
  bn.xor  w1, w1, w1
  bn.wsrw kmac_msg1, w1 /* 0 */
  /* Retrieve output. We keep the ephemeral shared key in masked form. */
  la      x5, kr
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x5++)
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.wsrr w0, kmac_digest1
  bn.sid  x0, 0(x5++)
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x5++)
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.wsrr w0, kmac_digest1
  bn.sid  x0, 0(x5++)

#else
  /* Compute kr = hash_g(m || h). */
  /* Send the message to KMAC. */
  addi    x5, x0, 64
  slli    x5, x5, 5
  addi    x5, x5, SHA3_512_CFG
  csrrw   x0, kmac_cfg, x5
  la      x5, m
  bn.lid  x0, 0(x5)
  bn.wsrw kmac_msg, w0 /* m */
  la      x5, dptr_h
  lw      x5, 0(x5)
  bn.lid  x0, 0(x5)
  bn.wsrw kmac_msg, w0 /* h */

  la      x5, kr
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x5++)
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x5++)
#endif

  /*** shake256(z||c,32) ***/
  addi    x11, x0, 32
  la      x5, ctbytes
  lw      x5, 0(x5)
  add     x11, x11, x5
  slli    x5, x11, 5
  addi    x5, x5, SHAKE256_CFG
#ifdef HARDENED
  addi    x6, x0, 1
  slli    x6, x6, 20
  add     x5, x5, x6
#endif
  csrrw   x0, kmac_cfg, x5
  /* z */
  la      x5, dptr_h
  lw      x5, 0(x5)
  bn.lid  x0, 32(x5)
  bn.wsrw kmac_msg, w0
#ifdef HARDENED
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.lid  x0, 64(x5)
  bn.wsrw kmac_msg1, w0
#endif

  /* c */
  la   x5, dptr_ct
  lw   x10, 0(x5)
  la   x5, ctbytes
  lw   x5, 0(x5)
  srli x5, x5, 5
#ifdef HARDENED
  loop x5, 3
    bn.lid  x0, 0(x10++)
    bn.wsrw kmac_msg, w0
    bn.wsrw kmac_msg1, w31
  endloop
  la      x5, ss_false
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x5++)
  bn.xor  w0, w0, w0 /* Whitening. */
  bn.wsrr w0, kmac_digest1
  bn.sid  x0, 0(x5)
#else
  loop x5, 2
    bn.lid  x0, 0(x10++)
    bn.wsrw kmac_msg, w0
  endloop
  la      x5, ss_false
  bn.wsrr w0, kmac_digest
  bn.sid  x0, 0(x5)
#endif

  /* Compute re-encryption and compare the re-encrypted ciphertext with the
   * public ciphertext. w0 contains the comparison result. */
  la   x10, m
  la   x5, dptr_pk
  lw   x11, 0(x5)
  la   x12, kr /* coins */
#ifdef HARDENED
  addi x12, x12, 64
#else
  addi x12, x12, 32
#endif
  la   x5, dptr_ct
  lw   x13, 0(x5)
  addi x14, x0, NSHARES
  la   x5, k
  lw   x15, 0(x5)
  jal  x1, indcpa_enc_cmp

#ifndef HARDENED
  /*** cmov ***/
  la      x5, kr
  addi    x4, x0, 1
  bn.lid  x4++, 0(x5) /* load true key */
  la      x5, ss_false
  bn.lid  x4, 0(x5) /* load false key */
  bn.xor  w3, w1, w2
  bn.and  w3, w3, w0 /* w0 is the comparison result: 0 if equal, all ones otherwise. */
  bn.xor  w0, w1, w3
  la      x5, dptr_ss
  lw      x5, 0(x5)
  bn.sid  x0, 0(x5)
  ret
#else
  /*** cmov ***/
  la      x5, kr
  la      x6, dptr_ss
  lw      x6, 0(x6)
  la      x7, ss_false
  addi    x4, x0, 1
  bn.xor  w1, w1, w1
  bn.addi w1, w1, 1
  bn.cmp  w0, w1
  csrrw   x28, fg0, x0
  srli    x28, x28, 3 /* extract z flag */
  beq     x28, x0, _fail
  bn.lid  x0, 0(x5)
  bn.lid  x4, 32(x5)
  beq     x0, x0, _end
_fail:
  bn.lid  x0, 0(x7)
  bn.lid  x4, 32(x7)
  beq     x0, x0, _end
_end:
  bn.sid  x0, 0(x6)
  bn.sid  x4, 32(x6)
  ret

#endif
