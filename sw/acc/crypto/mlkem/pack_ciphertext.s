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
 * Name: poly_compress
 *
 * Return r = Compressq(x, d) = round((2^d / q) * x) mod 2^d for d in {4, 5}.
 *
 * @param[in]  x10: dmem pointer to x
 * @param[out] x11: dmem pointer to r
 * @param[in]  x12: k, the security level
 * @param[in]  w31: all-zero register
 *
 * clobbered registers: x4 to x5, x10 to x11, w0 to w5, w16, w30
 * clobbered flag groups: FG0
 */

.globl poly_compress
.type poly_compress, @function
poly_compress:
    /* Load constants. */
    la     x5, modulus_over_2
    addi   x4, x0, 2
    bn.lid x4, 0(x5) /* w2 = (0x681)^16 */
    la     x5, const_1290167
    addi   x4, x0, 5
    bn.lid x4, 0(x5) /* w5 = const_1290167 */

    addi x4, x0, 4
    beq  x12, x4, _handle_k4_poly_compress

_handle_kn4_poly_compress:
    /* Multiply the constant 80635 with 2**4 so that later we shift to the right
     * 32 bits instead of 28 bits. This means we can return the high parts of
     * the 64-bit products within the multiplication instruction. */
    bn.mov  w30, w16
    bn.subi w16, w5, 7 /* w16 = 80635 * 16 = 1290160 */

    loopi 4, 16
        loopi 4, 14
            bn.lid               x0, 0(x10++)
            bn.shv.16h           w0, w0 << 4   /* <= 4 */
            bn.addv.16h          w0, w0, w2    /* += 1665 */
            bn.trn1.16h          w1, w0, w31   /* Put even coeffs to 32-bit slots. */
            bn.mulv.l.8s.even.hi w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
            bn.mulv.l.8s.odd.hi  w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
            bn.trn2.16h          w0, w0, w31   /* Put odd coeffs to 32-bit slots. */
            bn.mulv.l.8s.even.hi w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
            bn.mulv.l.8s.odd.hi  w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
            bn.trn1.16h          w1, w1, w0
            loopi 16, 2
                bn.rshi w4, w1, w4 >> 4
                bn.rshi w1, w31, w1 >> 16
            endloop
            nop
        endloop
        bn.sid x4, 0(x11++)
    endloop

    bn.mov w16, w30
    ret

_handle_k4_poly_compress:
    bn.shv.8s w3, w2 >> 17 /* w3 = (0x340)^8 */
    bn.shv.8s w3, w3 << 1  /* w3 = (0x680)^8 */
    /* Multiply the constant 40318 with 2**5 (1290176) so that later we shift to the
     * right 32 bits instead of 28 bits. This means we can return the high parts of
     * the 64-bit products within the multiplication instruction. */
    bn.mov  w30, w16
    bn.addi w16, w5, 9 /* w16 = 1290176 */

    /* 1 */
    loopi 3, 6
        bn.lid x0, 0(x10++)
        jal    x1, _poly_compress_16
        loopi 16, 2
            bn.rshi w4, w1, w4 >> 5
            bn.rshi w1, w31, w1 >> 16
        endloop
        nop
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_compress_16
    loopi 3, 2
        bn.rshi w4, w1, w4 >> 5
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 1
    bn.sid  x4, 0(x11++)

    /* 2 */
    loopi 13, 2
        bn.rshi w4, w1, w4 >> 5
        bn.rshi w1, w31, w1 >> 16
    endloop
    loopi 2, 6
        bn.lid x0, 0(x10++)
        jal    x1, _poly_compress_16
        loopi 16, 2
            bn.rshi w4, w1, w4 >> 5
            bn.rshi w1, w31, w1 >> 16
        endloop
        nop
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_compress_16
    loopi 6, 2
        bn.rshi w4, w1, w4 >> 5
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 2
    bn.sid  x4, 0(x11++)

    /* 3 */
    loopi 10, 2
        bn.rshi w4, w1, w4 >> 5
        bn.rshi w1, w31, w1 >> 16
    endloop
    loopi 2, 6
        bn.lid x0, 0(x10++)
        jal    x1, _poly_compress_16
        loopi 16, 2
            bn.rshi w4, w1, w4 >> 5
            bn.rshi w1, w31, w1 >> 16
        endloop
        nop
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_compress_16
    loopi 9, 2
        bn.rshi w4, w1, w4 >> 5
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 3
    bn.sid  x4, 0(x11++)

    /* 4 */
    loopi 7, 2
        bn.rshi w4, w1, w4 >> 5
        bn.rshi w1, w31, w1 >> 16
    endloop
    loopi 2, 6
        bn.lid x0, 0(x10++)
        jal    x1, _poly_compress_16
        loopi 16, 2
            bn.rshi w4, w1, w4 >> 5
            bn.rshi w1, w31, w1 >> 16
        endloop
        nop
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_compress_16
    loopi 12, 2
        bn.rshi w4, w1, w4 >> 5
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 4
    bn.sid  x4, 0(x11++)

    /* 5 */
    loopi 4, 2
        bn.rshi w4, w1, w4 >> 5
        bn.rshi w1, w31, w1 >> 16
    endloop
    loopi 3, 6
        bn.lid x0, 0(x10++)
        jal    x1, _poly_compress_16
        loopi 16, 2
            bn.rshi w4, w1, w4 >> 5
            bn.rshi w1, w31, w1 >> 16
        endloop
        nop
    endloop
    bn.sid x4, 0(x11++)

    bn.mov w16, w30
    ret

/*
 * Name: _poly_compress_16
 *
 * Description: Subroutine of poly_compress for compressing 16 coefficients
 *
 * @param[in]  w0: input vector with 16 16-bit coefficients
 * @param[out] w1: output vector with 16 compressed coefficients
 * @param[in]  w3: (0x680)^8
 * @param[in]  w16 (sw0): const_1290176
 * @param[in]  w31: all-zero register
 *
 * clobbered registers: w0 to w1
 * clobbered flag groups: none
 */

_poly_compress_16:
  bn.trn1.16h          w1, w0, w31   /* Put even coeffs to 32-bit slots. */
  bn.shv.8s            w1, w1 << 5   /* << 5 */
  bn.addv.8s           w1, w1, w3    /* +1664 */
  bn.mulv.l.8s.even.hi w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.mulv.l.8s.odd.hi  w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.trn2.16h          w0, w0, w31   /* Put odd coeffs to 32-bit slots. */
  bn.shv.8s            w0, w0 << 5   /* << 5 */
  bn.addv.8s           w0, w0, w3    /* +1664 */
  bn.mulv.l.8s.even.hi w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.mulv.l.8s.odd.hi  w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.trn1.16h          w1, w1, w0
  ret

/*
 * Name: poly_polyvec_compress
 *
 * Return r = Compressq(x, d) = round((2^d / q) * x) mod 2^d for d in {10, 11}.
 *
 * @param[in]  x10: dmem pointer to x
 * @param[out] x11: dmem pointer to r
 * @param[in]  x12: k, the security level
 * @param[in]  w31: all-zero register
 *
 * clobbered registers: x4 to x5, x10 to x11, w0 to w5, w16, w30
 * clobbered flag groups: FG0
 */

.globl poly_polyvec_compress
.type poly_polyvec_compress, @function
poly_polyvec_compress:
    /* Load constants. */
    la     x5, modulus_over_2
    addi   x4, x0, 2
    bn.lid x4, 0(x5) /* w2 = (0x681)^16 */
    la     x5, const_1290167
    addi   x4, x0, 5
    bn.lid x4, 0(x5) /* w5 = const_1290167 */

    addi x4, x0, 4
    beq  x12, x4, _handle_k4_poly_polyvec_compress

_handle_kn4_poly_polyvec_compress:
    bn.shv.8s w3, w2 >> 16 /* w3 = (0x681)^8 */
    bn.mov    w30, w16
    bn.mov    w16, w5      /* w16 = (1290167) */

    loopi 2, 61
        /* 1 */
        bn.lid x0, 0(x10++)
        jal    x1, _poly_polyvec_compress_16_kn4
        loopi 16, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.lid x0, 0(x10++)
        jal    x1, _poly_polyvec_compress_16_kn4
        loopi 9, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.rshi w4, w1, w4 >> 6
        bn.sid  x4, 0(x11++)

        /* 2 */
        loopi 7, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.lid x0, 0(x10++)
        jal    x1, _poly_polyvec_compress_16_kn4
        loopi 16, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.lid x0, 0(x10++)
        jal    x1, _poly_polyvec_compress_16_kn4
        loopi 3, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.rshi w4, w1, w4 >> 2
        bn.sid  x4, 0(x11++)

        /* 3 */
        loopi 13, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.lid x0, 0(x10++)
        jal    x1, _poly_polyvec_compress_16_kn4
        loopi 12, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.rshi w4, w1, w4 >> 8
        bn.sid  x4, 0(x11++)

        /* 4 */
        loopi 4, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.lid x0, 0(x10++)
        jal    x1, _poly_polyvec_compress_16_kn4
        loopi 16, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.lid x0, 0(x10++)
        jal    x1, _poly_polyvec_compress_16_kn4
        loopi 6, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.rshi w4, w1, w4 >> 4
        bn.sid  x4, 0(x11++)

        /* 5 */
        loopi 10, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.lid x0, 0(x10++)
        jal    x1, _poly_polyvec_compress_16_kn4
        loopi 16, 2
            bn.rshi w4, w1, w4 >> 10
            bn.rshi w1, w31, w1 >> 16
        endloop
        bn.sid  x4, 0(x11++)
    endloop

    bn.mov w16, w30
    ret

_handle_k4_poly_polyvec_compress:
    bn.shv.8s w3, w2 >> 17 /* w3 = (0x340)^8 */
    bn.shv.8s w3, w3 << 1  /* w3 = (0x680)^8 */
    /* Multiply the constant 645084 with 2 (1290168) so that later we shift to the
     * right 32 bits instead of 28 bits. This means we can return the high parts of
     * the 64-bit products within the multiplication instruction. */
    bn.mov  w30, w16
    bn.addi w16, w5, 1 /* w16 = 1290168 */

    /* 1 */
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 16, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 7, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 3
    bn.sid  x4, 0(x11++)

    /* 2 */
    loopi 9, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 14, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 6
    bn.sid  x4, 0(x11++)

    /* 3 */
    loopi 2, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 16, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 5, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 9
    bn.sid  x4, 0(x11++)

    /* 4 */
    loopi 11, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 13, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 1
    bn.sid  x4, 0(x11++)

    /* 5 */
    loopi 3, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 16, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 4, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 4
    bn.sid  x4, 0(x11++)

    /* 6 */
    loopi 12, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 11, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 7
    bn.sid  x4, 0(x11++)

    /* 7 */
    loopi 5, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 16, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 2, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 10
    bn.sid  x4, 0(x11++)

    /* 8 */
    loopi 14, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 10, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 2
    bn.sid  x4, 0(x11++)

    /* 9 */
    loopi 6, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 16, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    bn.rshi w4, w1, w4 >> 11
    bn.rshi w1, w31, w1 >> 16
    bn.rshi w4, w1, w4 >> 5
    bn.sid  x4, 0(x11++)

    /* 10 */
    loopi 15, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 8, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.rshi w4, w1, w4 >> 8
    bn.sid  x4, 0(x11++)

    /* 11 */
    loopi 8, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.lid x0, 0(x10++)
    jal    x1, _poly_polyvec_compress_16_k4
    loopi 16, 2
        bn.rshi w4, w1, w4 >> 11
        bn.rshi w1, w31, w1 >> 16
    endloop
    bn.sid x4, 0(x11++)

    bn.mov w16, w30
    ret

/*
 * Name: _poly_polyvec_compress_16_kn4
 *
 * Description: Subroutine of poly_polyvec_compress for compressing 16
 *              coefficients for KYBER_K = {2, 3}.
 *
 * @param[in]  w0: input vector with 16 16-bit coefficients
 * @param[out] w1: output vector with 16 compressed coefficients
 * @param[in]  w3: (0x681)^8
 * @param[in]  w16 (sw0): const_1290167
 * @param[in]  w31: all-zero register
 *
 * clobbered registers: w0 to w1
 * clobbered flag groups: none
 */

_poly_polyvec_compress_16_kn4:
  bn.trn1.16h          w1, w0, w31   /* Put even coeffs to 32-bit slots. */
  bn.shv.8s            w1, w1 << 10  /* << 10 */
  bn.addv.8s           w1, w1, w3    /* +1665 */
  bn.mulv.l.8s.even.hi w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.mulv.l.8s.odd.hi  w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.trn2.16h          w0, w0, w31   /* Put odd coeffs to 32-bit slots. */
  bn.shv.8s            w0, w0 << 10  /* << 10 */
  bn.addv.8s           w0, w0, w3    /* +1665 */
  bn.mulv.l.8s.even.hi w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.mulv.l.8s.odd.hi  w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.trn1.16h          w1, w1, w0
  ret


/*
 * Name: _poly_polyvec_compress_16_k4
 *
 * Description: Subroutine of poly_polyvec_compress for compressing 16
 *              coefficients for KYBER_K = 4.
 *
 * @param[in]  w0: input vector with 16 16-bit coefficients
 * @param[out] w1: output vector with 16 compressed coefficients
 * @param[in]  w3: (0x680)^8
 * @param[in]  w16 (sw0): const_1290168
 * @param[in]  w31: all-zero register
 *
 * clobbered registers: w0 to w1
 * clobbered flag groups: none
 */

_poly_polyvec_compress_16_k4:
  bn.trn1.16h          w1, w0, w31   /* Put even coeffs to 32-bit slots. */
  bn.shv.8s            w1, w1 << 11  /* << 11 */
  bn.addv.8s           w1, w1, w3    /* +1664 */
  bn.mulv.l.8s.even.hi w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.mulv.l.8s.odd.hi  w1, w1, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.trn2.16h          w0, w0, w31   /* Put odd coeffs to 32-bit slots. */
  bn.shv.8s            w0, w0 << 11  /* << 11 */
  bn.addv.8s           w0, w0, w3    /* +1664 */
  bn.mulv.l.8s.even.hi w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.mulv.l.8s.odd.hi  w0, w0, sw0.0 /* >> 32 = high parts of 64-bit products. */
  bn.trn1.16h          w1, w1, w0
  ret
