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

;; code to compute SHA512 by-2 using SSE
;; outer calling routine takes care of save and restore of XMM registers
;; Logic designed/laid out by JDG

;; Function clobbers: rax, rcx, rdx,   rbx, rsi, rdi, r9-r15; ymm0-15
;; Stack must be aligned to 16 bytes before call
;; Windows clobbers:  rax         rdx             r8 r9 r10 r11    
;; Windows preserves:     rbx rcx     rsi rdi rbp               r12 r13 r14 r15
;;
;; Linux clobbers:    rax             rsi         r8 r9 r10 r11    
;; Linux preserves:       rbx rcx rdx     rdi rbp               r12 r13 r14 r15
;;
;; clobbers xmm0-15

%include "mb_mgr_datastruct.asm"

;%define DO_DBGPRINT
%include "dbgprint.asm"

%ifdef LINUX ; Linux definitions
 %define arg1    rdi
 %define arg2    rsi
%else ; Windows definitions
 %define arg1    rcx
 %define arg2    rdx
%endif

; Common definitions
%define STATE    arg1
%define INP_SIZE arg2

%define IDX     rax
%define ROUND	r8
%define TBL	r11

%define inp0 r9
%define inp1 r10

%define a xmm0
%define b xmm1
%define c xmm2
%define d xmm3
%define e xmm4
%define f xmm5
%define g xmm6
%define h xmm7

%define a0 xmm8
%define a1 xmm9
%define a2 xmm10

%define TT0 xmm14
%define TT1 xmm13
%define TT2 xmm12
%define TT3 xmm11
%define TT4 xmm10
%define TT5 xmm9

%define T1  xmm14
%define TMP xmm15



%define SZ2	2*SHA512_DIGEST_WORD_SIZE	; Size of one vector register
%define ROUNDS 80*SZ2

; Define stack usage

struc STACK
_DATA:		resb	SZ2 * 16
_DIGEST:	resb	SZ2 * NUM_SHA512_DIGEST_WORDS
		resb	8 	; for alignment, must be odd multiple of 8
endstruc

%define MOVPD	movupd

; transpose r0, r1, t0
; Input looks like {r0 r1}
; r0 = {a1 a0}
; r1 = {b1 b0}
;
; output looks like 
; r0 = {b0, a0}
; t0 = {b1, a1}

%macro TRANSPOSE 3
%define %%r0 %1
%define %%r1 %2
%define %%t0 %3
	movapd  %%t0, %%r0		; t0 = a1 a0
	shufpd	%%r0, %%r1, 00b		; r0 = b0 a0
	shufpd	%%t0, %%r1, 11b		; t0 = b1 a1
%endm


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
	movdqa	%%tmp, %%reg
	psllq  	%%tmp, (64-(%%imm))
	psrlq	%%reg, %%imm
	por		%%reg, %%tmp
%endmacro

; PRORQ dst/src, amt
%macro PRORQ 2
	PRORQ	%1, %2, TMP
%endmacro


;; arguments passed implicitly in preprocessor symbols i, a...h
%macro ROUND_00_15 2
%define %%T1 %1
%define %%i  %2
	movdqa	a0, e		; sig1: a0 = e
	movdqa	a1, e		; sig1: s1 = e
	PRORQ	a0, (18-14)	; sig1: a0 = (e >> 4)

	movdqa	a2, f		; ch: a2 = f
	pxor	a2, g		; ch: a2 = f^g
	pand	a2, e		; ch: a2 = (f^g)&e
	pxor	a2, g		; a2 = ch

	PRORQ	a1, 41		; sig1: a1 = (e >> 41)
        movdqa	[SZ2*(%%i&0xf) + rsp],%%T1
	paddq	%%T1,[TBL + ROUND]	; T1 = W + K
	pxor	a0, e		; sig1: a0 = e ^ (e >> 5)
	PRORQ	a0, 14		; sig1: a0 = (e >> 14) ^ (e >> 18)
	paddq	h, a2		; h = h + ch
	movdqa	a2, a		; sig0: a2 = a
	PRORQ	a2, (34-28)	; sig0: a2 = (a >> 6)
	paddq	h, %%T1		; h = h + ch + W + K
	pxor	a0, a1		; a0 = sigma1
	movdqa	a1, a		; sig0: a1 = a
	movdqa	%%T1, a		; maj: T1 = a
	PRORQ	a1, 39		; sig0: a1 = (a >> 39)
	pxor	%%T1, c		; maj: T1 = a^c
	add	ROUND, SZ2	; ROUND++
	pand	%%T1, b		; maj: T1 = (a^c)&b
	paddq	h, a0

	paddq	d, h

	pxor	a2, a		; sig0: a2 = a ^ (a >> 11)
	PRORQ	a2, 28		; sig0: a2 = (a >> 28) ^ (a >> 34)
	pxor	a2, a1		; a2 = sig0
	movdqa	a1, a		; maj: a1 = a
	pand	a1, c		; maj: a1 = a&c
	por	a1, %%T1	; a1 = maj
	paddq	h, a1		; h = h + ch + W + K + maj
	paddq	h, a2		; h = h + ch + W + K + maj + sigma0

	ROTATE_ARGS
%endm


;; arguments passed implicitly in preprocessor symbols i, a...h
%macro ROUND_16_XX 2
%define %%T1 %1
%define %%i  %2
	movdqa	%%T1, [SZ2*((%%i-15)&0xf) + rsp]
	movdqa	a1, [SZ2*((%%i-2)&0xf) + rsp]
	movdqa	a0, %%T1
	PRORQ	%%T1, 8-1
	movdqa	a2, a1
	PRORQ	a1, 61-19
	pxor	%%T1, a0
	PRORQ	%%T1, 1
	pxor	a1, a2
	PRORQ	a1, 19
	psrlq	a0, 7
	pxor	%%T1, a0
	psrlq	a2, 6
	pxor	a1, a2
	paddq	%%T1, [SZ2*((%%i-16)&0xf) + rsp]
	paddq	a1, [SZ2*((%%i-7)&0xf) + rsp]
	paddq	%%T1, a1

	ROUND_00_15 %%T1, %%i
%endm



;; SHA512_ARGS:
;;   UINT128 digest[8];  // transposed digests
;;   UINT8  *data_ptr[2];
;; 

;; void sha512_x2_sse(SHA512_ARGS *args, UINT64 num_blocks); 
;; arg 1 : STATE    : pointer args
;; arg 2 : INP_SIZE : size of data in blocks (assumed >= 1)
;;
global sha512_x2_sse :function
align 32
sha512_x2_sse:
	; general registers preserved in outer calling routine
	; outer calling routine saves all the XMM registers
	sub	rsp, STACK_size

	;; Load the pre-transposed incoming digest. 
	movdqa	a,[STATE + 0 * SHA512_DIGEST_ROW_SIZE]
	movdqa	b,[STATE + 1 * SHA512_DIGEST_ROW_SIZE]
	movdqa	c,[STATE + 2 * SHA512_DIGEST_ROW_SIZE]
	movdqa	d,[STATE + 3 * SHA512_DIGEST_ROW_SIZE]
	movdqa	e,[STATE + 4 * SHA512_DIGEST_ROW_SIZE]
	movdqa	f,[STATE + 5 * SHA512_DIGEST_ROW_SIZE]
	movdqa	g,[STATE + 6 * SHA512_DIGEST_ROW_SIZE]
	movdqa	h,[STATE + 7 * SHA512_DIGEST_ROW_SIZE]

	DBGPRINTL_XMM "incoming transposed sha512 digest", a, b, c, d, e, f, g, h 
	lea	TBL,[K512_2 wrt rip]
	
	;; load the address of each of the 2 message lanes
	;; getting ready to transpose input onto stack
	mov	inp0,[STATE + _data_ptr_sha512  +0*PTR_SZ]
	mov	inp1,[STATE + _data_ptr_sha512  +1*PTR_SZ]

	xor	IDX, IDX
lloop:
	xor	ROUND, ROUND
	DBGPRINTL64  "lloop enter INP_SIZE ", INP_SIZE 
	DBGPRINTL64 " IDX = ", IDX
	;; save old digest
	movdqa	[rsp + _DIGEST + 0*SZ2], a
	movdqa	[rsp + _DIGEST + 1*SZ2], b
	movdqa	[rsp + _DIGEST + 2*SZ2], c
	movdqa	[rsp + _DIGEST + 3*SZ2], d
	movdqa	[rsp + _DIGEST + 4*SZ2], e
	movdqa	[rsp + _DIGEST + 5*SZ2], f
	movdqa	[rsp + _DIGEST + 6*SZ2], g
	movdqa	[rsp + _DIGEST + 7*SZ2], h

	DBGPRINTL "incoming data["
%assign i 0
%rep 8
	;; load up the shuffler for little-endian to big-endian format
	movdqa	TMP, [PSHUFFLE_BYTE_FLIP_MASK wrt rip] 
	MOVPD	TT0,[inp0+IDX+i*16] ;; double precision is 64 bits
	MOVPD	TT2,[inp1+IDX+i*16]
	DBGPRINTL_XMM "input message block", TT0
	TRANSPOSE	TT0, TT2, TT1
	pshufb	TT0, TMP 
	pshufb	TT1, TMP
	ROUND_00_15	TT0,(i*2+0) 
	ROUND_00_15	TT1,(i*2+1) 
%assign i (i+1)
%endrep
	DBGPRINTL "]"
	add	IDX, 8 * 16 ;; increment by a message block 
	

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
	paddq	a, [rsp + _DIGEST + 0*SZ2]
	paddq	b, [rsp + _DIGEST + 1*SZ2]
	paddq	c, [rsp + _DIGEST + 2*SZ2]
	paddq	d, [rsp + _DIGEST + 3*SZ2]
	paddq	e, [rsp + _DIGEST + 4*SZ2]
	paddq	f, [rsp + _DIGEST + 5*SZ2]
	paddq	g, [rsp + _DIGEST + 6*SZ2]
	paddq	h, [rsp + _DIGEST + 7*SZ2]
 
	sub	INP_SIZE, 1  ;; unit is blocks
	jne	lloop

	; write back to memory (state object) the transposed digest
	movdqa	[STATE + 0*SHA512_DIGEST_ROW_SIZE],a
	movdqa	[STATE + 1*SHA512_DIGEST_ROW_SIZE],b
	movdqa	[STATE + 2*SHA512_DIGEST_ROW_SIZE],c
	movdqa	[STATE + 3*SHA512_DIGEST_ROW_SIZE],d
	movdqa	[STATE + 4*SHA512_DIGEST_ROW_SIZE],e
	movdqa	[STATE + 5*SHA512_DIGEST_ROW_SIZE],f
	movdqa	[STATE + 6*SHA512_DIGEST_ROW_SIZE],g
	movdqa	[STATE + 7*SHA512_DIGEST_ROW_SIZE],h
	DBGPRINTL_XMM "exit transposed digest ", a, b, c, d, e, f, g, h

	; update input pointers
	add	inp0, IDX
	mov	[STATE + _data_ptr_sha512  + 0*PTR_SZ], inp0
	add	inp1, IDX
	mov	[STATE + _data_ptr_sha512  + 1*PTR_SZ], inp1

	;;;;;;;;;;;;;;;;
	;; Postamble

	add	rsp, STACK_size
DBGPRINTL "====================== exit sha512_x2_sse code =====================\n"
	ret

section .data
align 64
global K512_2
K512_2:
	ddq	0x428a2f98d728ae22428a2f98d728ae22
	ddq	0x7137449123ef65cd7137449123ef65cd
	ddq	0xb5c0fbcfec4d3b2fb5c0fbcfec4d3b2f
	ddq	0xe9b5dba58189dbbce9b5dba58189dbbc
	ddq	0x3956c25bf348b5383956c25bf348b538
	ddq	0x59f111f1b605d01959f111f1b605d019
	ddq	0x923f82a4af194f9b923f82a4af194f9b
	ddq	0xab1c5ed5da6d8118ab1c5ed5da6d8118
	ddq	0xd807aa98a3030242d807aa98a3030242
	ddq	0x12835b0145706fbe12835b0145706fbe
	ddq	0x243185be4ee4b28c243185be4ee4b28c
	ddq	0x550c7dc3d5ffb4e2550c7dc3d5ffb4e2
	ddq	0x72be5d74f27b896f72be5d74f27b896f
	ddq	0x80deb1fe3b1696b180deb1fe3b1696b1
	ddq	0x9bdc06a725c712359bdc06a725c71235
	ddq	0xc19bf174cf692694c19bf174cf692694
	ddq	0xe49b69c19ef14ad2e49b69c19ef14ad2
	ddq	0xefbe4786384f25e3efbe4786384f25e3
	ddq	0x0fc19dc68b8cd5b50fc19dc68b8cd5b5
	ddq	0x240ca1cc77ac9c65240ca1cc77ac9c65
	ddq	0x2de92c6f592b02752de92c6f592b0275
	ddq	0x4a7484aa6ea6e4834a7484aa6ea6e483
	ddq	0x5cb0a9dcbd41fbd45cb0a9dcbd41fbd4
	ddq	0x76f988da831153b576f988da831153b5
	ddq	0x983e5152ee66dfab983e5152ee66dfab
	ddq	0xa831c66d2db43210a831c66d2db43210
	ddq	0xb00327c898fb213fb00327c898fb213f
	ddq	0xbf597fc7beef0ee4bf597fc7beef0ee4
	ddq	0xc6e00bf33da88fc2c6e00bf33da88fc2
	ddq	0xd5a79147930aa725d5a79147930aa725
	ddq	0x06ca6351e003826f06ca6351e003826f
	ddq	0x142929670a0e6e70142929670a0e6e70
	ddq	0x27b70a8546d22ffc27b70a8546d22ffc
	ddq	0x2e1b21385c26c9262e1b21385c26c926
	ddq	0x4d2c6dfc5ac42aed4d2c6dfc5ac42aed
	ddq	0x53380d139d95b3df53380d139d95b3df
	ddq	0x650a73548baf63de650a73548baf63de
	ddq	0x766a0abb3c77b2a8766a0abb3c77b2a8
	ddq	0x81c2c92e47edaee681c2c92e47edaee6
	ddq	0x92722c851482353b92722c851482353b
	ddq	0xa2bfe8a14cf10364a2bfe8a14cf10364
	ddq	0xa81a664bbc423001a81a664bbc423001
	ddq	0xc24b8b70d0f89791c24b8b70d0f89791
	ddq	0xc76c51a30654be30c76c51a30654be30
	ddq	0xd192e819d6ef5218d192e819d6ef5218
	ddq	0xd69906245565a910d69906245565a910
	ddq	0xf40e35855771202af40e35855771202a
	ddq	0x106aa07032bbd1b8106aa07032bbd1b8
	ddq	0x19a4c116b8d2d0c819a4c116b8d2d0c8
	ddq	0x1e376c085141ab531e376c085141ab53
	ddq	0x2748774cdf8eeb992748774cdf8eeb99
	ddq	0x34b0bcb5e19b48a834b0bcb5e19b48a8
	ddq	0x391c0cb3c5c95a63391c0cb3c5c95a63
	ddq	0x4ed8aa4ae3418acb4ed8aa4ae3418acb
	ddq	0x5b9cca4f7763e3735b9cca4f7763e373
	ddq	0x682e6ff3d6b2b8a3682e6ff3d6b2b8a3
	ddq	0x748f82ee5defb2fc748f82ee5defb2fc
	ddq	0x78a5636f43172f6078a5636f43172f60
	ddq	0x84c87814a1f0ab7284c87814a1f0ab72
	ddq	0x8cc702081a6439ec8cc702081a6439ec
	ddq	0x90befffa23631e2890befffa23631e28
	ddq	0xa4506cebde82bde9a4506cebde82bde9
	ddq	0xbef9a3f7b2c67915bef9a3f7b2c67915
	ddq	0xc67178f2e372532bc67178f2e372532b
	ddq	0xca273eceea26619cca273eceea26619c
	ddq	0xd186b8c721c0c207d186b8c721c0c207
	ddq	0xeada7dd6cde0eb1eeada7dd6cde0eb1e
	ddq	0xf57d4f7fee6ed178f57d4f7fee6ed178
	ddq	0x06f067aa72176fba06f067aa72176fba
	ddq	0x0a637dc5a2c898a60a637dc5a2c898a6
	ddq	0x113f9804bef90dae113f9804bef90dae
	ddq	0x1b710b35131c471b1b710b35131c471b
	ddq	0x28db77f523047d8428db77f523047d84
	ddq	0x32caab7b40c7249332caab7b40c72493
	ddq	0x3c9ebe0a15c9bebc3c9ebe0a15c9bebc
	ddq	0x431d67c49c100d4c431d67c49c100d4c
	ddq	0x4cc5d4becb3e42b64cc5d4becb3e42b6
	ddq	0x597f299cfc657e2a597f299cfc657e2a
	ddq	0x5fcb6fab3ad6faec5fcb6fab3ad6faec
	ddq	0x6c44198c4a4758176c44198c4a475817

PSHUFFLE_BYTE_FLIP_MASK: ddq	0x08090a0b0c0d0e0f0001020304050607


