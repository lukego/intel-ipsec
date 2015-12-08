;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Copyright (c) 2015, Intel Corporation 
; 
; All rights reserved. 
; 
; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met: 
; 
; * Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.  
; 
; * Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the
;   distribution. 
; 
; * Neither the name of the Intel Corporation nor the names of its
;   contributors may be used to endorse or promote products derived from
;   this software without specific prior written permission. 
; 
; 
; THIS SOFTWARE IS PROVIDED BY INTEL CORPORATION ""AS IS"" AND ANY
; EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
; PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL INTEL CORPORATION OR
; CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
; EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
; PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
; PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
; LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; code to compute quad SHA512 using AVX
;; use YMMs to tackle the larger digest size
;; outer calling routine takes care of save and restore of XMM registers
;; Logic designed/laid out by JDG

;; Function clobbers: rax, rcx, rdx,   rbx, rsi, rdi, r9-r15; ymm0-15
;; Stack must be aligned to 32 bytes before call
;; Windows clobbers:  rax rbx     rdx             r8 r9 r10 r11 r12 
;; Windows preserves:         rcx     rsi rdi rbp                   r13 r14 r15
;;
;; Linux clobbers:    rax rbx rcx rdx rsi         r8 r9 r10 r11 r12 
;; Linux preserves:           rcx rdx     rdi rbp                   r13 r14 r15
;;
;; clobbers ymm0-15

;%define DO_DBGPRINT
%include "dbgprint.asm"

%include "mb_mgr_datastruct.asm"

%ifdef LINUX
%define arg1 	        rdi
%define arg2		rsi
%else
%define arg1 	        rcx
%define arg2		rdx
%endif

; Common definitions
%define STATE    arg1
%define INP_SIZE arg2

%define IDX     rax
%define ROUND	rbx
%define TBL      r8

%define inp0 r9
%define inp1 r10
%define inp2 r11
%define inp3 r12

%define a ymm0
%define b ymm1
%define c ymm2
%define d ymm3
%define e ymm4
%define f ymm5
%define g ymm6
%define h ymm7

%define a0 ymm8
%define a1 ymm9
%define a2 ymm10

%define TT0 ymm14
%define TT1 ymm13
%define TT2 ymm12
%define TT3 ymm11
%define TT4 ymm10
%define TT5 ymm9

%define T1  ymm14
%define TMP ymm15



%define SZ4	4*SHA512_DIGEST_WORD_SIZE	; Size of one vector register
%define ROUNDS 80*SZ4

; Define stack usage

;; Assume stack aligned to 32 bytes before call
;; Therefore FRAMESZ mod 32 must be 32-8 = 24
struc stack_frame
  .data		resb	16*SZ4
  .digest	resb	NUM_SHA512_DIGEST_WORDS*SZ4
  .align	resb	24
endstruc

%define _DIGEST stack_frame.digest

%define VMOVPD	vmovupd

; operates on YMMs
; transpose r0, r1, r2, r3, t0, t1
; "transpose" data in {r0..r3} using temps {t0..t3}
; Input looks like: {r0 r1 r2 r3}
; r0 = {a7 a6 a5 a4 a3 a2 a1 a0}
; r1 = {b7 b6 b5 b4 b3 b2 b1 b0}
; r2 = {c7 c6 c5 c4 c3 c2 c1 c0}
; r3 = {d7 d6 d5 d4 d3 d2 d1 d0}
;
; output looks like: {t0 r1 r0 r3}
; t0 = {d1 d0 c1 c0 b1 b0 a1 a0}
; r1 = {d3 d2 c3 c2 b3 b2 a3 a2}
; r0 = {d5 d4 c5 c4 b5 b4 a5 a4}
; r3 = {d7 d6 c7 c6 b7 b6 a7 a6}
; 
%macro TRANSPOSE 6
%define %%r0 %1
%define %%r1 %2
%define %%r2 %3
%define %%r3 %4
%define %%t0 %5
%define %%t1 %6
	; vshufps does not cross the mid-way boundary and hence is cheaper
	vshufps	%%t0, %%r0, %%r1, 0x44	; t0 = {b5 b4 a5 a4 b1 b0 a1 a0}
	vshufps	%%r0, %%r0, %%r1, 0xEE	; r0 = {b7 b6 a7 a6 b3 b2 a3 a2}

	vshufps	%%t1, %%r2, %%r3, 0x44	; t1 = {d5 d4 c5 c4 d1 d0 c1 c0}
	vshufps	%%r2, %%r2, %%r3, 0xEE	; r2 = {d7 d6 c7 c6 d3 d2 c3 c2}

	vperm2f128 %%r1, %%r0, %%r2, 0x20; r1 = {d3 d2 c3 c2 b3 b2 a3 a2}

	vperm2f128 %%r3, %%r0, %%r2, 0x31; r3 = {d7 d6 c7 c6 b7 b6 a7 a6}

	vperm2f128 %%r0, %%t0, %%t1, 0x31; r0 = {d5 d4 c5 c4 b5 b4 a5 a4}
    
	; now ok to clobber t0
	vperm2f128 %%t0, %%t0, %%t1, 0x20; t0 = {d1 d0 c1 c0 b1 b0 a1 a0}

%endmacro	


%macro ROTATE_ARGS 0
%xdefine TMP_ h
%xdefine h g
%xdefine g f
%xdefine f e
%xdefine e d
%xdefine d c
%xdefine c b
%xdefine b a
%xdefine a TMP_
%endm

; PRORQ reg, imm, tmp
; packed-rotate-right-double
; does a rotate by doing two shifts and an or
%macro PRORQ 3
%define %%reg %1
%define %%imm %2
%define %%tmp %3
	vpsllq	%%tmp, %%reg, (64-(%%imm))
	vpsrlq	%%reg, %%reg, %%imm
	vpor	%%reg, %%reg, %%tmp
%endmacro

; non-destructive
; PRORQ_nd reg, imm, tmp, src
%macro PRORQ_nd 4
%define %%reg %1
%define %%imm %2
%define %%tmp %3
%define %%src %4
	vpsllq	%%tmp, %%src, (64-(%%imm))
	vpsrlq	%%reg, %%src, %%imm
	vpor	%%reg, %%reg, %%tmp
%endmacro

; PRORQ dst/src, amt
%macro PRORQ 2
	PRORQ	%1, %2, TMP
%endmacro

; PRORQ_nd dst, src, amt
%macro PRORQ_nd 3
	PRORQ_nd	%1, %3, TMP, %2
%endmacro



;; arguments passed implicitly in preprocessor symbols i, a...h
%macro ROUND_00_15 2
%define %%T1 %1
%define %%i  %2
	PRORQ_nd a0, e, (18-14)	; sig1: a0 = (e >> 4)

	vpxor	a2, f, g	; ch: a2 = f^g
	vpand	a2, a2, e	; ch: a2 = (f^g)&e
	vpxor	a2, a2, g	; a2 = ch

	PRORQ_nd a1, e, 41	; sig1: a1 = (e >> 41)
        vmovdqa	[SZ4*(%%i&0xf) + rsp],%%T1
	vpaddq	%%T1,%%T1,[TBL + ROUND]	; T1 = W + K
	vpxor	a0, a0, e	; sig1: a0 = e ^ (e >> 5)
	PRORQ	a0, 14		; sig1: a0 = (e >> 14) ^ (e >> 18)
	vpaddq	h, h, a2	; h = h + ch
	PRORQ_nd a2, a, (34-28)	; sig0: a2 = (a >> 6)
	vpaddq	h, h, %%T1	; h = h + ch + W + K
	vpxor	a0, a0, a1	; a0 = sigma1
	vmovdqa	%%T1, a		; maj: T1 = a
	PRORQ_nd a1, a, 39	; sig0: a1 = (a >> 39)
	vpxor	%%T1, %%T1, c	; maj: T1 = a^c
	add	ROUND, SZ4 ; ROUND++
	vpand	%%T1, %%T1, b	; maj: T1 = (a^c)&b
	vpaddq	h, h, a0

	vpaddq	d, d, h

	vpxor	a2, a2, a	; sig0: a2 = a ^ (a >> 11)
	PRORQ	a2, 28		; sig0: a2 = (a >> 28) ^ (a >> 34)
	vpxor	a2, a2, a1	; a2 = sig0
	vpand	a1, a, c	; maj: a1 = a&c
	vpor	a1, a1, %%T1	; a1 = maj
	vpaddq	h, h, a1	; h = h + ch + W + K + maj
	vpaddq	h, h, a2	; h = h + ch + W + K + maj + sigma0
	ROTATE_ARGS
  
%endm


;; arguments passed implicitly in preprocessor symbols i, a...h
%macro ROUND_16_XX 2
%define %%T1 %1
%define %%i  %2
	vmovdqa	%%T1, [SZ4*((%%i-15)&0xf) + rsp]
	vmovdqa	a1, [SZ4*((%%i-2)&0xf) + rsp]
	vmovdqa	a0, %%T1
	PRORQ	%%T1, 8-1
	vmovdqa	a2, a1
	PRORQ	a1, 61-19
	vpxor	%%T1, %%T1, a0
	PRORQ	%%T1, 1
	vpxor	a1, a1, a2
	PRORQ	a1, 19
	vpsrlq	a0, a0, 7
	vpxor	%%T1, %%T1, a0
	vpsrlq	a2, a2, 6
	vpxor	a1, a1, a2
	vpaddq	%%T1, %%T1, [SZ4*((%%i-16)&0xf) + rsp]
	vpaddq	a1, a1, [SZ4*((%%i-7)&0xf) + rsp]
	vpaddq	%%T1, %%T1, a1

	ROUND_00_15 %%T1, %%i

%endm


;; void sha512_x4_avx2(void *STATE, const int INP_SIZE)
;; arg 1 : STATE    : pointer to input data
;; arg 2 : INP_SIZE : size of data in blocks (assumed >= 1)
global sha512_x4_avx2 :function
align 32
sha512_x4_avx2:
	; general registers preserved in outer calling routine
	; outer calling routine saves all the XMM registers

	sub	rsp, stack_frame_size

     ;; Load the pre-transposed incoming digest. 
	vmovdqu a, [STATE+ 0*SHA512_DIGEST_ROW_SIZE]
	vmovdqu b, [STATE+ 1*SHA512_DIGEST_ROW_SIZE]
	vmovdqu c, [STATE+ 2*SHA512_DIGEST_ROW_SIZE] 
	vmovdqu d, [STATE+ 3*SHA512_DIGEST_ROW_SIZE] 
	vmovdqu e, [STATE+ 4*SHA512_DIGEST_ROW_SIZE] 
	vmovdqu f, [STATE+ 5*SHA512_DIGEST_ROW_SIZE] 
	vmovdqu g, [STATE+ 6*SHA512_DIGEST_ROW_SIZE] 
	vmovdqu h, [STATE+ 7*SHA512_DIGEST_ROW_SIZE] 

	DBGPRINTL_YMM "sha512-avx2 Incoming digest", a, b, c, d, e, f, g, h 
	lea	TBL,[K512_4 wrt rip]
    
	;; load the address of each of the MAX_LANES (4)  message lanes
	;; getting ready to transpose input onto stack
	mov	inp0,[STATE + _data_ptr_sha512 + 0*PTR_SZ]
	mov	inp1,[STATE + _data_ptr_sha512 + 1*PTR_SZ]
	mov	inp2,[STATE + _data_ptr_sha512 + 2*PTR_SZ]
	mov	inp3,[STATE + _data_ptr_sha512 + 3*PTR_SZ]

	xor	IDX, IDX
lloop:
	xor	ROUND, ROUND

	;; save old digest
	vmovdqa	[rsp + _DIGEST + 0*SZ4], a
	vmovdqa	[rsp + _DIGEST + 1*SZ4], b
	vmovdqa	[rsp + _DIGEST + 2*SZ4], c
	vmovdqa	[rsp + _DIGEST + 3*SZ4], d
	vmovdqa	[rsp + _DIGEST + 4*SZ4], e
	vmovdqa	[rsp + _DIGEST + 5*SZ4], f
	vmovdqa	[rsp + _DIGEST + 6*SZ4], g
	vmovdqa	[rsp + _DIGEST + 7*SZ4], h

%assign i 0
%rep 4
	;; load up the shuffler for little-endian to big-endian format
	vmovdqa	TMP, [PSHUFFLE_BYTE_FLIP_MASK wrt rip] 
	VMOVPD	TT2,[inp0+IDX+i*32]
	VMOVPD	TT1,[inp1+IDX+i*32]
	VMOVPD	TT4,[inp2+IDX+i*32]
	VMOVPD	TT3,[inp3+IDX+i*32]
	TRANSPOSE	TT2, TT1, TT4, TT3, TT0, TT5
	DBGPRINTL_YMM "sha512-avx2 Incoming data", TT1, TT2, TT3, TT4
	vpshufb	TT0, TT0, TMP 
	vpshufb	TT1, TT1, TMP
	vpshufb	TT2, TT2, TMP
	vpshufb	TT3, TT3, TMP
	ROUND_00_15	TT0,(i*4+0) 
	ROUND_00_15	TT1,(i*4+1) 
	ROUND_00_15	TT2,(i*4+2) 
	ROUND_00_15	TT3,(i*4+3) 
%assign i (i+1)
%endrep
;; Increment IDX by message block size == 8 (loop) * 16 (XMM width in bytes)
	add	IDX, 4 * 32
    
%assign i (i*4)

	jmp	Lrounds_16_xx
align 16
Lrounds_16_xx:
%rep 16
	ROUND_16_XX	T1, i
%assign i (i+1)
%endrep

	cmp	ROUND,ROUNDS
	jb	Lrounds_16_xx
   
	;; add old digest
	vpaddq	a, a, [rsp + _DIGEST + 0*SZ4]
	vpaddq	b, b, [rsp + _DIGEST + 1*SZ4]
	vpaddq	c, c, [rsp + _DIGEST + 2*SZ4]
	vpaddq	d, d, [rsp + _DIGEST + 3*SZ4]
	vpaddq	e, e, [rsp + _DIGEST + 4*SZ4]
	vpaddq	f, f, [rsp + _DIGEST + 5*SZ4]
	vpaddq	g, g, [rsp + _DIGEST + 6*SZ4]
	vpaddq	h, h, [rsp + _DIGEST + 7*SZ4]
 
	sub	INP_SIZE, 1 ;; consumed one message block 
	jne	lloop

	; write back to memory (state object) the transposed digest
	vmovdqu	[STATE+ 0*SHA512_DIGEST_ROW_SIZE ],a
	vmovdqu	[STATE+ 1*SHA512_DIGEST_ROW_SIZE ],b
	vmovdqu	[STATE+ 2*SHA512_DIGEST_ROW_SIZE ],c
	vmovdqu	[STATE+ 3*SHA512_DIGEST_ROW_SIZE ],d
	vmovdqu	[STATE+ 4*SHA512_DIGEST_ROW_SIZE ],e
	vmovdqu	[STATE+ 5*SHA512_DIGEST_ROW_SIZE ],f
	vmovdqu	[STATE+ 6*SHA512_DIGEST_ROW_SIZE ],g
	vmovdqu	[STATE+ 7*SHA512_DIGEST_ROW_SIZE ],h
   DBGPRINTL_YMM "sha512-avx2 Outgoing digest", a, b, c, d, e, f, g, h 
    
	;; update input data pointers
	add inp0, IDX
	mov	[STATE + _data_ptr_sha512 + 0*PTR_SZ], inp0
	add inp1, IDX
	mov	[STATE + _data_ptr_sha512 + 1*PTR_SZ], inp1
	add inp2, IDX
	mov	[STATE + _data_ptr_sha512 + 2*PTR_SZ], inp2
	add inp3, IDX
	mov	[STATE + _data_ptr_sha512 + 3*PTR_SZ], inp3

	;;;;;;;;;;;;;;;;
	;; Postamble

	add rsp, stack_frame_size

	; outer calling routine restores XMM and other GP registers
	ret

section .data
align 64
K512_4:
	ddq 0x428a2f98d728ae22428a2f98d728ae22, 0x428a2f98d728ae22428a2f98d728ae22
	ddq 0x7137449123ef65cd7137449123ef65cd, 0x7137449123ef65cd7137449123ef65cd
	ddq 0xb5c0fbcfec4d3b2fb5c0fbcfec4d3b2f, 0xb5c0fbcfec4d3b2fb5c0fbcfec4d3b2f
	ddq 0xe9b5dba58189dbbce9b5dba58189dbbc, 0xe9b5dba58189dbbce9b5dba58189dbbc
	ddq 0x3956c25bf348b5383956c25bf348b538, 0x3956c25bf348b5383956c25bf348b538
	ddq 0x59f111f1b605d01959f111f1b605d019, 0x59f111f1b605d01959f111f1b605d019
	ddq 0x923f82a4af194f9b923f82a4af194f9b, 0x923f82a4af194f9b923f82a4af194f9b
	ddq 0xab1c5ed5da6d8118ab1c5ed5da6d8118, 0xab1c5ed5da6d8118ab1c5ed5da6d8118
	ddq 0xd807aa98a3030242d807aa98a3030242, 0xd807aa98a3030242d807aa98a3030242
	ddq 0x12835b0145706fbe12835b0145706fbe, 0x12835b0145706fbe12835b0145706fbe
	ddq 0x243185be4ee4b28c243185be4ee4b28c, 0x243185be4ee4b28c243185be4ee4b28c
	ddq 0x550c7dc3d5ffb4e2550c7dc3d5ffb4e2, 0x550c7dc3d5ffb4e2550c7dc3d5ffb4e2
	ddq 0x72be5d74f27b896f72be5d74f27b896f, 0x72be5d74f27b896f72be5d74f27b896f
	ddq 0x80deb1fe3b1696b180deb1fe3b1696b1, 0x80deb1fe3b1696b180deb1fe3b1696b1
	ddq 0x9bdc06a725c712359bdc06a725c71235, 0x9bdc06a725c712359bdc06a725c71235
	ddq 0xc19bf174cf692694c19bf174cf692694, 0xc19bf174cf692694c19bf174cf692694
	ddq 0xe49b69c19ef14ad2e49b69c19ef14ad2, 0xe49b69c19ef14ad2e49b69c19ef14ad2
	ddq 0xefbe4786384f25e3efbe4786384f25e3, 0xefbe4786384f25e3efbe4786384f25e3
	ddq 0x0fc19dc68b8cd5b50fc19dc68b8cd5b5, 0x0fc19dc68b8cd5b50fc19dc68b8cd5b5
	ddq 0x240ca1cc77ac9c65240ca1cc77ac9c65, 0x240ca1cc77ac9c65240ca1cc77ac9c65
	ddq 0x2de92c6f592b02752de92c6f592b0275, 0x2de92c6f592b02752de92c6f592b0275
	ddq 0x4a7484aa6ea6e4834a7484aa6ea6e483, 0x4a7484aa6ea6e4834a7484aa6ea6e483
	ddq 0x5cb0a9dcbd41fbd45cb0a9dcbd41fbd4, 0x5cb0a9dcbd41fbd45cb0a9dcbd41fbd4
	ddq 0x76f988da831153b576f988da831153b5, 0x76f988da831153b576f988da831153b5
	ddq 0x983e5152ee66dfab983e5152ee66dfab, 0x983e5152ee66dfab983e5152ee66dfab
	ddq 0xa831c66d2db43210a831c66d2db43210, 0xa831c66d2db43210a831c66d2db43210
	ddq 0xb00327c898fb213fb00327c898fb213f, 0xb00327c898fb213fb00327c898fb213f
	ddq 0xbf597fc7beef0ee4bf597fc7beef0ee4, 0xbf597fc7beef0ee4bf597fc7beef0ee4
	ddq 0xc6e00bf33da88fc2c6e00bf33da88fc2, 0xc6e00bf33da88fc2c6e00bf33da88fc2
	ddq 0xd5a79147930aa725d5a79147930aa725, 0xd5a79147930aa725d5a79147930aa725
	ddq 0x06ca6351e003826f06ca6351e003826f, 0x06ca6351e003826f06ca6351e003826f
	ddq 0x142929670a0e6e70142929670a0e6e70, 0x142929670a0e6e70142929670a0e6e70
	ddq 0x27b70a8546d22ffc27b70a8546d22ffc, 0x27b70a8546d22ffc27b70a8546d22ffc
	ddq 0x2e1b21385c26c9262e1b21385c26c926, 0x2e1b21385c26c9262e1b21385c26c926
	ddq 0x4d2c6dfc5ac42aed4d2c6dfc5ac42aed, 0x4d2c6dfc5ac42aed4d2c6dfc5ac42aed
	ddq 0x53380d139d95b3df53380d139d95b3df, 0x53380d139d95b3df53380d139d95b3df
	ddq 0x650a73548baf63de650a73548baf63de, 0x650a73548baf63de650a73548baf63de
	ddq 0x766a0abb3c77b2a8766a0abb3c77b2a8, 0x766a0abb3c77b2a8766a0abb3c77b2a8
	ddq 0x81c2c92e47edaee681c2c92e47edaee6, 0x81c2c92e47edaee681c2c92e47edaee6
	ddq 0x92722c851482353b92722c851482353b, 0x92722c851482353b92722c851482353b
	ddq 0xa2bfe8a14cf10364a2bfe8a14cf10364, 0xa2bfe8a14cf10364a2bfe8a14cf10364
	ddq 0xa81a664bbc423001a81a664bbc423001, 0xa81a664bbc423001a81a664bbc423001
	ddq 0xc24b8b70d0f89791c24b8b70d0f89791, 0xc24b8b70d0f89791c24b8b70d0f89791
	ddq 0xc76c51a30654be30c76c51a30654be30, 0xc76c51a30654be30c76c51a30654be30
	ddq 0xd192e819d6ef5218d192e819d6ef5218, 0xd192e819d6ef5218d192e819d6ef5218
	ddq 0xd69906245565a910d69906245565a910, 0xd69906245565a910d69906245565a910
	ddq 0xf40e35855771202af40e35855771202a, 0xf40e35855771202af40e35855771202a
	ddq 0x106aa07032bbd1b8106aa07032bbd1b8, 0x106aa07032bbd1b8106aa07032bbd1b8
	ddq 0x19a4c116b8d2d0c819a4c116b8d2d0c8, 0x19a4c116b8d2d0c819a4c116b8d2d0c8
	ddq 0x1e376c085141ab531e376c085141ab53, 0x1e376c085141ab531e376c085141ab53
	ddq 0x2748774cdf8eeb992748774cdf8eeb99, 0x2748774cdf8eeb992748774cdf8eeb99
	ddq 0x34b0bcb5e19b48a834b0bcb5e19b48a8, 0x34b0bcb5e19b48a834b0bcb5e19b48a8
	ddq 0x391c0cb3c5c95a63391c0cb3c5c95a63, 0x391c0cb3c5c95a63391c0cb3c5c95a63
	ddq 0x4ed8aa4ae3418acb4ed8aa4ae3418acb, 0x4ed8aa4ae3418acb4ed8aa4ae3418acb
	ddq 0x5b9cca4f7763e3735b9cca4f7763e373, 0x5b9cca4f7763e3735b9cca4f7763e373
	ddq 0x682e6ff3d6b2b8a3682e6ff3d6b2b8a3, 0x682e6ff3d6b2b8a3682e6ff3d6b2b8a3
	ddq 0x748f82ee5defb2fc748f82ee5defb2fc, 0x748f82ee5defb2fc748f82ee5defb2fc
	ddq 0x78a5636f43172f6078a5636f43172f60, 0x78a5636f43172f6078a5636f43172f60
	ddq 0x84c87814a1f0ab7284c87814a1f0ab72, 0x84c87814a1f0ab7284c87814a1f0ab72
	ddq 0x8cc702081a6439ec8cc702081a6439ec, 0x8cc702081a6439ec8cc702081a6439ec
	ddq 0x90befffa23631e2890befffa23631e28, 0x90befffa23631e2890befffa23631e28
	ddq 0xa4506cebde82bde9a4506cebde82bde9, 0xa4506cebde82bde9a4506cebde82bde9
	ddq 0xbef9a3f7b2c67915bef9a3f7b2c67915, 0xbef9a3f7b2c67915bef9a3f7b2c67915
	ddq 0xc67178f2e372532bc67178f2e372532b, 0xc67178f2e372532bc67178f2e372532b
	ddq 0xca273eceea26619cca273eceea26619c, 0xca273eceea26619cca273eceea26619c
	ddq 0xd186b8c721c0c207d186b8c721c0c207, 0xd186b8c721c0c207d186b8c721c0c207
	ddq 0xeada7dd6cde0eb1eeada7dd6cde0eb1e, 0xeada7dd6cde0eb1eeada7dd6cde0eb1e
	ddq 0xf57d4f7fee6ed178f57d4f7fee6ed178, 0xf57d4f7fee6ed178f57d4f7fee6ed178
	ddq 0x06f067aa72176fba06f067aa72176fba, 0x06f067aa72176fba06f067aa72176fba
	ddq 0x0a637dc5a2c898a60a637dc5a2c898a6, 0x0a637dc5a2c898a60a637dc5a2c898a6
	ddq 0x113f9804bef90dae113f9804bef90dae, 0x113f9804bef90dae113f9804bef90dae
	ddq 0x1b710b35131c471b1b710b35131c471b, 0x1b710b35131c471b1b710b35131c471b
	ddq 0x28db77f523047d8428db77f523047d84, 0x28db77f523047d8428db77f523047d84
	ddq 0x32caab7b40c7249332caab7b40c72493, 0x32caab7b40c7249332caab7b40c72493
	ddq 0x3c9ebe0a15c9bebc3c9ebe0a15c9bebc, 0x3c9ebe0a15c9bebc3c9ebe0a15c9bebc
	ddq 0x431d67c49c100d4c431d67c49c100d4c, 0x431d67c49c100d4c431d67c49c100d4c
	ddq 0x4cc5d4becb3e42b64cc5d4becb3e42b6, 0x4cc5d4becb3e42b64cc5d4becb3e42b6
	ddq 0x597f299cfc657e2a597f299cfc657e2a, 0x597f299cfc657e2a597f299cfc657e2a
	ddq 0x5fcb6fab3ad6faec5fcb6fab3ad6faec, 0x5fcb6fab3ad6faec5fcb6fab3ad6faec
	ddq 0x6c44198c4a4758176c44198c4a475817, 0x6c44198c4a4758176c44198c4a475817

align 32
PSHUFFLE_BYTE_FLIP_MASK: ddq 0x08090a0b0c0d0e0f0001020304050607
                         ddq 0x18191a1b1c1d1e1f1011121314151617


