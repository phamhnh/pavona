/* Copyright zeroRISC Inc. */
/* Modified by Authors of "Towards ML-KEM & ML-DSA on OpenTitan" (https://eprint.iacr.org/2024/1192). */
/* Copyright "Towards ML-KEM & ML-DSA on OpenTitan" Authors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.text

/* Config to start a SHAKE-256 operation. */
#define SHAKE256_CFG 0xA

/*
 * Name: poly_getnoise_eta_init
 *
 * Prepares for polynomial CBD sampling via either of
 * `poly_getnoise_eta_1` or `poly_getnoise_eta_2` given a seed and
 * a nonce by initializing a SHAKE256 operation.
 *
 * @param[in]  x10: dmem pointer to input seed
 * @param[in]  x11: dmem pointer to nonce
 *
 * clobbered registers: x5, w0
 * clobbered flag groups: none
 */

.globl poly_getnoise_eta_init
.type poly_getnoise_eta_init, @function
poly_getnoise_eta_init:
  /* Initialize a SHAKE256 operation. */
  addi  x5, x0, 33
  slli  x5, x5, 5
  addi  x5, x5, SHAKE256_CFG
  csrrw x0, kmac_cfg, x5

  /* Send the message to the Keccak core. */
  bn.lid  x0, 0(x10)
  bn.wsrw kmac_msg, w0
  li      x5, 1
  csrrw   x0, kmac_partial_write, x5
  bn.lid  x0, 0(x11)
  bn.wsrw kmac_msg, w0
  ret

/*
 * Name: poly_getnoise_eta_1
 *
 * Sample a polynomial deterministically from a seed and a nonce,
 * with output polynomial close to centered binomial distribution
 * with parameter KYBER_ETA1; this function assumes
 * `poly_getnoise_eta_init` has been called first with the
 * appropriate seed and nonce.
 *
 * @param[in]  x10: eta
 * @param[out] x11: dmem pointer to output polynomial
 *
 * clobbered registers: x4 to x5, x11, w0 to w11, w20 to w21
 * clobbered flag groups: FG0
 */

.globl poly_getnoise_eta_1
.type poly_getnoise_eta_1, @function
poly_getnoise_eta_1:
  addi x4, x0, 3
  beq  x10, x4, _handle_cbd3
  jal  x1, cbd2
  ret

_handle_cbd3:
  jal x1, cbd3
  ret

/*
 * Name: poly_getnoise_eta_2
 *
 * Sample a polynomial deterministically from a seed and a nonce,
 * with output polynomial close to centered binomial distribution
 * with parameter KYBER_ETA2; this function assumes
 * `poly_getnoise_eta_init` has been called first with the
 * appropriate seed and nonce.
 *
 * @param[in]  x10: eta
 * @param[out] x11: dmem pointer to output polynomial
 *
 * clobbered registers: x4 to x5, x11, w0 to w4, w6 to w8
 * clobbered flag groups: FG0
 */

.globl poly_getnoise_eta_2
.type poly_getnoise_eta_2, @function
poly_getnoise_eta_2:
  jal x1, cbd2
  ret

/*
 * Name: cbd2
 *
 * Given an array of uniformly random bytes, compute
 * polynomial with coefficients distributed according to
 * a centered binomial distribution with parameter eta=2.
 *
 * @param[out] x11: dmem pointer to output polynomial
 * @param[in]  kmac_digest: SHAKE-256 squeeze set up by poly_getnoise_eta_init
 * @param[in]  mod: q = 3329
 * @param[in]  w31: all-zero register
 *
 * clobbered registers: x4 to x5, x11, w0 to w4, w6 to w8
 * clobbered flag groups: FG0
 */

.globl cbd2
.type cbd2, @function
cbd2:
  la     x5, cbd2_const
  addi   x4, x0, 3
  bn.lid x4++, 0(x5)
  bn.lid x4, 32(x5)

  /* Create mask 0xff. */
  bn.subi    w8, w31, 1
  bn.shv.16h w8, w8 >> 12

  addi x4, x0, 2
  loopi 4, 19
    bn.wsrr w0, kmac_digest
    bn.and  w1, w0, w3        /* Extract even bits. */
    bn.rshi w0, w31, w0 >> 1  /* w0 >> 1 */
    bn.and  w0, w0, w3        /* Extract odd bits. */
    bn.add  w0, w0, w1        /* Add even and odd bits. */
    bn.and  w1, w0, w4        /* Extract even bit pair. */
    bn.rshi w0, w31, w0 >> 2  /* w0 >> 2 */
    bn.and  w0, w0, w4        /* Extract odd bit pair. */

    loopi 4,  9
      loopi 16, 4
        bn.rshi w6, w1, w6 >> 16
        bn.rshi w7, w0, w7 >> 16
        bn.rshi w1, w31, w1 >> 4
        bn.rshi w0, w31, w0 >> 4
      endloop
      bn.and       w6, w6, w8
      bn.and       w7, w7, w8
      bn.subvm.16h w2, w6, w7
      bn.sid       x4, 0(x11++)
    endloop
    nop
  endloop
  ret

/*
 * Name: cbd3
 *
 * Given an array of uniformly random bytes, compute
 * polynomial with coefficients distributed according to
 * a centered binomial distribution with parameter eta=3.
 * This function is only needed for Kyber-512.
 *
 * @param[out] x11: dmem pointer to output polynomial
 * @param[in]  kmac_digest: SHAKE-256 squeeze set up by poly_getnoise_eta_init
 * @param[in]  mod: q = 3329
 * @param[in]  w31: all-zero register
 *
 * clobbered registers: x4 to x5, x11, w0 to w11, w20 to w21
 * clobbered flag groups: FG0
 */

.globl cbd3
.type cbd3, @function
cbd3:
  la     x5, cbd3_const
  addi   x4, x0, 20
  bn.lid x4++, 0(x5)
  bn.lid x4, 32(x5)

  /* Create mask 0x7. */
  bn.subi    w10, w31, 1
  bn.shv.16h w10, w10 >> 13

  addi x5, x0, 11
  loopi 2, 114
    bn.wsrr w0, kmac_digest
    bn.wsrr w1, kmac_digest
    bn.wsrr w2, kmac_digest

    bn.and  w3, w0, w20       /* Extract bit i mod 3 = 0. */
    bn.rshi w4, w31, w0 >> 1  /* w0 >> 1 */
    bn.and  w4, w4, w20       /* Extract bit i mod 3 = 1 bit. */
    bn.rshi w5, w31, w0 >> 2  /* w0 >> 1 */
    bn.and  w5, w5, w20       /* Extract bit mod 3 = 2 bit. */
    bn.add  w3, w3, w4
    bn.add  w3, w3, w5

    bn.rshi w0, w1, w0 >> 255
    bn.and  w4, w0, w20
    bn.rshi w5, w31, w0 >> 1
    bn.and  w5, w5, w20
    bn.rshi w6, w31, w0 >> 2
    bn.and  w6, w6, w20
    bn.add  w4, w4, w5
    bn.add  w4, w4, w6

    bn.rshi w0, w2, w1 >> 254
    bn.and  w5, w0, w20
    bn.rshi w6, w31, w0 >> 1
    bn.and  w6, w6, w20
    bn.rshi w7, w31, w0 >> 2
    bn.and  w7, w7, w20
    bn.add  w5, w5, w6
    bn.add  w5, w5, w7

    bn.rshi w0, w31, w2 >> 253
    bn.and  w6, w0, w20
    bn.rshi w0, w31, w0 >> 1
    bn.and  w7, w0, w20
    bn.rshi w0, w31, w0 >> 1
    bn.and  w0, w0, w20
    bn.add  w6, w6, w7
    bn.add  w6, w6, w0

    bn.and  w0, w3, w21       /* & 0x000111 */
    bn.rshi w3, w31, w3 >> 3  /* w3 >> 3 */
    bn.and  w3, w3, w21       /* & 0x000111 */

    bn.and  w1, w4, w21
    bn.rshi w4, w31, w4 >> 3
    bn.and  w4, w4, w21

    bn.and  w2, w5, w21
    bn.rshi w5, w31, w5 >> 3
    bn.and  w5, w5, w21

    loopi 2, 9
      loopi 16, 4
        bn.rshi w8, w0, w8 >> 16
        bn.rshi w9, w3, w9 >> 16
        bn.rshi w0, w31, w0 >> 6
        bn.rshi w3, w31, w3 >> 6
      endloop
      bn.and       w8, w8, w10
      bn.and       w9, w9, w10
      bn.subvm.16h w11, w8, w9
      bn.sid       x5, 0(x11++)
    endloop
    loopi 10, 4
      bn.rshi w8, w0, w8 >> 16
      bn.rshi w9, w3, w9 >> 16
      bn.rshi w0, w31, w0 >> 6
      bn.rshi w3, w31, w3 >> 6
    endloop
    bn.rshi w8, w0, w8 >> 16
    bn.rshi w9, w1, w9 >> 16
    bn.rshi w1, w31, w1 >> 6
    loopi 5, 4
      bn.rshi w8, w4, w8 >> 16
      bn.rshi w9, w1, w9 >> 16
      bn.rshi w1, w31, w1 >> 6
      bn.rshi w4, w31, w4 >> 6
    endloop
    bn.and       w8, w8, w10
    bn.and       w9, w9, w10
    bn.subvm.16h w11, w8, w9
    bn.sid       x5, 0(x11++)

    loopi 2, 9
      loopi 16, 4
        bn.rshi w8, w4, w8 >> 16
        bn.rshi w9, w1, w9 >> 16
        bn.rshi w1, w31, w1 >> 6
        bn.rshi w4, w31, w4 >> 6
      endloop
      bn.and       w8, w8, w10
      bn.and       w9, w9, w10
      bn.subvm.16h w11, w8, w9
      bn.sid       x5, 0(x11++)
    endloop
    loopi 5, 4
      bn.rshi w8, w4, w8 >> 16
      bn.rshi w9, w1, w9 >> 16
      bn.rshi w1, w31, w1 >> 6
      bn.rshi w4, w31, w4 >> 6
    endloop
    loopi 11, 4
      bn.rshi w8, w2, w8 >> 16
      bn.rshi w9, w5, w9 >> 16
      bn.rshi w2, w31, w2 >> 6
      bn.rshi w5, w31, w5 >> 6
    endloop
    bn.and       w8, w8, w10
    bn.and       w9, w9, w10
    bn.subvm.16h w11, w8, w9
    bn.sid       x5, 0(x11++)

    loopi 16, 4
      bn.rshi w8, w2, w8 >> 16
      bn.rshi w9, w5, w9 >> 16
      bn.rshi w2, w31, w2 >> 6
      bn.rshi w5, w31, w5 >> 6
    endloop
    bn.and       w8, w8, w10
    bn.and       w9, w9, w10
    bn.subvm.16h w11, w8, w9
    bn.sid       x5, 0(x11++)
    loopi 15, 4
      bn.rshi w8, w2, w8 >> 16
      bn.rshi w9, w5, w9 >> 16
      bn.rshi w2, w31, w2 >> 6
      bn.rshi w5, w31, w5 >> 6
    endloop
    bn.rshi      w8, w2, w8 >> 16
    bn.rshi      w9, w6, w9 >> 16
    bn.and       w8, w8, w10
    bn.and       w9, w9, w10
    bn.subvm.16h w11, w8, w9
    bn.sid       x5, 0(x11++)
  endloop
  ret
