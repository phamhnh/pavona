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

/*
 * Name: poly_frommsg
 *
 * Convert 32-byte message to polynomial.
 *
 * @param[in]  x10: dmem pointer to input byte array
 * @param[out] x11: dmem pointer to output polynomial
 * @param[in]  w31: all-zero register
 *
 * clobbered registers: x4 to x5, x11, w0 to w1, w3
 * clobbered flag groups: FG0
 */

.globl poly_frommsg
.type poly_frommsg, @function
poly_frommsg:
  la     x5, modulus_over_2
  addi   x4, x0, 3
  bn.lid x4, 0(x5)

  addi   x4, x0, 1
  bn.lid x0, 0(x10)
  loopi 16, 7
    loopi 16, 3
      bn.rshi w1, w0, w1 >> 1
      bn.rshi w1, w31, w1 >> 15
      bn.rshi w0, w31, w0 >> 1
    endloop
    bn.subv.16h w1, w31, w1
    bn.and      w1, w1, w3
    bn.sid      x4, 0(x11++)
  endloop
  ret

/*
 * Name: poly_tomsg
 *
 * Convert polynomial to 32-byte message.
 *
 * @param[in]  x10: dmem pointer to input polynomial
 * @param[out] x11: dmem pointer to output byte array
 * @param[in]  w31: all-zero register
 *
 * clobbered registers: x4 to x5, x10, w0 to w3, w16, w30
 * clobbered flag groups: FG0
 */

.globl poly_tomsg
.type poly_tomsg, @function
poly_tomsg:
  /* Load constants. */
  la     x5, modulus_over_2
  addi   x4, x0, 2
  bn.lid x4, 0(x5) /* w2 = (0x681)^16 */
  bn.mov w30, w16
  la     x5, const_1290167
  addi   x4, x0, 16
  bn.lid x4, 0(x5) /* w16 = 1290167 */

  /* Multiply the constant 80635 with 2**4 so that later we shift to the right
   * 32 bits instead of 28 bits. This means we can return the high parts of
   * the 64-bit products within the multiplication instruction. */
  bn.subi w16, w16, 7 /* w16 = 1290160 = 80635 << 4 */

  loopi 16, 14
    bn.lid               x0, 0(x10++)
    bn.shv.16h           w0, w0 << 1   /* <= 1 */
    bn.addv.16h          w0, w0, w2    /* += 1665 */
    bn.trn1.16h          w1, w0, w31   /* Put even coeffs in 32-bit slots. */
    bn.mulv.l.8s.even.hi w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
    bn.mulv.l.8s.odd.hi  w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
    bn.trn2.16h          w0, w0, w31   /* Put odd coeffs to 32-bit slots. */
    bn.mulv.l.8s.even.hi w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
    bn.mulv.l.8s.odd.hi  w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
    bn.trn1.16h          w0, w1, w0
    loopi 16, 2
      bn.rshi w3, w0, w3 >> 1
      bn.rshi w0, w31, w0 >> 16
    endloop
    nop
  endloop
  addi   x4, x0, 3
  bn.sid x4, 0(x11)

  bn.mov w16, w30
  ret

/*
 * Name: poly_add
 *
 * Return r = (x + y) modulo any modulus q.
 *
 * @param[in]  x10: dmem pointer to x
 * @param[in]  x11: dmem pointer to y
 * @param[out] x12: dmem pointer to r
 * @param[in]  mod: the modulus q
 *
 * clobbered registers: x4, x10 to x12, w0 to w1
 * clobbered flag groups: none
 */

.globl poly_add
.type poly_add, @function
poly_add:
  addi x4, x0, 1
  loopi 16, 4
    bn.lid       x0, 0(x10++)
    bn.lid       x4, 0(x11++)
    bn.addvm.16h w0, w0, w1
    bn.sid       x0, 0(x12++)
  endloop
  ret

/*
 * Name: poly_sub
 *
 * Return r = (x - y) modulo any modulus q.
 *
 * @param[in]  x10: dmem pointer to x
 * @param[in]  x11: dmem pointer to y
 * @param[out] x12: dmem pointer to r
 * @param[in]  mod: the modulus q
 *
 * clobbered registers: x4, x10 to x12, w0 to w1
 * clobbered flag groups: none
 */

.globl poly_sub
.type poly_sub, @function
poly_sub:
  addi x4, x0, 1
  loopi 16, 4
    bn.lid       x0, 0(x10++)
    bn.lid       x4, 0(x11++)
    bn.subvm.16h w0, w0, w1
    bn.sid       x0, 0(x12++)
  endloop
  ret

/*
 * Name: poly_tomont (in-place)
 *
 * Put the input polynomial x out of Montgomery domain for ML-KEM with q = 3329.
 *
 * @param[in,out] x10: dmem pointer t0 x
 * @param[in]     w31: all-zero register
 *
 * clobbered registers: x4 to x5, x10, w0 to w1, acc, acch
 * clobbered flag groups: none
 */

.globl poly_tomont
.type poly_tomont, @function
poly_tomont:
  la     x5, const_tomont
  add    x4, x0, x0
  bn.lid x4++, 0(x5)

  loopi 16, 6
    bn.lid               x4, 0(x10)
    bn.mulv.16h.acc.z.lo w1, w0, w1
    bn.mulv.l.16h.lo     w1, w1, sw0.2
    bn.mulv.l.16h.acc.hi w1, w1, sw0.0
    bn.addvm.16h         w1, w1, w31
    bn.sid               x4, 0(x10++)
  endloop
  ret
