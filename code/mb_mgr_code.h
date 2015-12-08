/**********************************************************************
Copyright (c) 2015, Intel Corporation 

All rights reserved. 

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met: 

* Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.  

* Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the
  distribution. 

* Neither the name of the Intel Corporation nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission. 


THIS SOFTWARE IS PROVIDED BY INTEL CORPORATION ""AS IS"" AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL INTEL CORPORATION OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
**********************************************************************/


// This contains the bulk of the mb_mgr code, with #define's to build 
// an SSE, AVX, or AVX2 version (see mb_mgr_sse.c, mb_mgr_avx.c, etc.)

// get_next_job() returns a job object. This must be filled in and returned
// via submit_job() before get_next_job() is called again.
// submit_job() and flush_job() returns a job object. This job object ceases
// to be usable at the next call to get_next_job()

// index in JOBS array using byte offset rather than object index
#define JOBS(offset) ((JOB_AES_HMAC*)(((UINT64)state->jobs)+offset))

#define ADV_JOBS(ptr) \
    ptr += sizeof(JOB_AES_HMAC); \
    if (ptr == (MAX_JOBS * sizeof(JOB_AES_HMAC))) ptr = 0

#define LEN(STATE, L) ((UINT8)(((STATE)->lens >> ((L)*8)) & 0xFF))

static UINT32 auth_tag_len[7] = {12, 14, 16, 24, 32, 12, 12};  //IN BYTES SHA1 = 12, SHA_224 = 14, SHA_256 =16, SHA_384 = 24, SHA_512 =32, AES_XCBC = 12, MD5=12  

////////////////////////////////////////////////////////////////////////


JOB_AES_HMAC* SUBMIT_JOB_AES128_DEC(JOB_AES_HMAC* job);
JOB_AES_HMAC* SUBMIT_JOB_AES192_DEC(JOB_AES_HMAC* job);
JOB_AES_HMAC* SUBMIT_JOB_AES256_DEC(JOB_AES_HMAC* job);
JOB_AES_HMAC* SUBMIT_JOB_AES128_CNTR(JOB_AES_HMAC* job);
JOB_AES_HMAC* SUBMIT_JOB_AES192_CNTR(JOB_AES_HMAC* job);
JOB_AES_HMAC* SUBMIT_JOB_AES256_CNTR(JOB_AES_HMAC* job);


////////////////////////////////////////////////////////////////////////

__forceinline
JOB_AES_HMAC*
SUBMIT_JOB_AES_ENC(MB_MGR *state, JOB_AES_HMAC *job)
{
    if (CBC == job->cipher_mode) {
        if (16 == job->aes_key_len_in_bytes) {
            return SUBMIT_JOB_AES128_ENC(&state->aes128_ooo, job);
        } else if (24 == job->aes_key_len_in_bytes) {
             return SUBMIT_JOB_AES192_ENC(&state->aes192_ooo, job);
        } else { // assume 32
            return SUBMIT_JOB_AES256_ENC(&state->aes256_ooo, job);
        }
    } else { // assume CNTR
        if (16 == job->aes_key_len_in_bytes) {
            return SUBMIT_JOB_AES128_CNTR(job);
        } else if (24 == job->aes_key_len_in_bytes) {
             return SUBMIT_JOB_AES192_CNTR(job);
        } else { // assume 32
            return SUBMIT_JOB_AES256_CNTR(job);
        }
    }
}

__forceinline
JOB_AES_HMAC*
FLUSH_JOB_AES_ENC(MB_MGR *state, JOB_AES_HMAC *job)
{
    if (CBC == job->cipher_mode) {
        if (16 == job->aes_key_len_in_bytes) {
            return FLUSH_JOB_AES128_ENC(&state->aes128_ooo);
        } else if (24 == job->aes_key_len_in_bytes) {
              return FLUSH_JOB_AES192_ENC(&state->aes192_ooo);
        } else  {// assume 32
            return FLUSH_JOB_AES256_ENC(&state->aes256_ooo);
        }
    } else { // assume CNTR
        return NULL;
    }
}

__forceinline
JOB_AES_HMAC*
SUBMIT_JOB_AES_DEC(JOB_AES_HMAC *job)
{
    if (CBC == job->cipher_mode) {
        if (16 == job->aes_key_len_in_bytes) {
            return SUBMIT_JOB_AES128_DEC(job);
        } else if (24 == job->aes_key_len_in_bytes) {
            return SUBMIT_JOB_AES192_DEC(job);
        } else { // assume 32
            return SUBMIT_JOB_AES256_DEC(job);
        }
    } else { // assume CNTR
        if (16 == job->aes_key_len_in_bytes) {
            return SUBMIT_JOB_AES128_CNTR(job);
        } else if (24 == job->aes_key_len_in_bytes) {
             return SUBMIT_JOB_AES192_CNTR(job);
        } else { // assume 32
            return SUBMIT_JOB_AES256_CNTR(job);
        }
    }
}


__forceinline
JOB_AES_HMAC*
SUBMIT_JOB_HASH(MB_MGR *state, JOB_AES_HMAC *job)
{
#ifdef VERBOSE
    printf("--------Enter SUBMIT_JOB_HASH --------------\n");
#endif
    switch (job->hash_alg) {
    case SHA1:
        return SUBMIT_JOB_HMAC(&state->hmac_sha_1_ooo, job);
    case SHA_224:
        return SUBMIT_JOB_HMAC_SHA_224(&state->hmac_sha_224_ooo, job);
    case SHA_256:
        return SUBMIT_JOB_HMAC_SHA_256(&state->hmac_sha_256_ooo, job);
    case SHA_384:
        return SUBMIT_JOB_HMAC_SHA_384(&state->hmac_sha_384_ooo, job);
    case SHA_512:
        return SUBMIT_JOB_HMAC_SHA_512(&state->hmac_sha_512_ooo, job);
    case AES_XCBC:
        return SUBMIT_JOB_AES_XCBC(&state->aes_xcbc_ooo, job);
    default: // assume MD5
        return SUBMIT_JOB_HMAC_MD5(&state->hmac_md5_ooo, job);
    }
}

__forceinline
JOB_AES_HMAC*
FLUSH_JOB_HASH(MB_MGR *state, JOB_AES_HMAC *job)
{
    switch (job->hash_alg) {
    case SHA1:
        return FLUSH_JOB_HMAC(&state->hmac_sha_1_ooo);
    case SHA_224:
        return FLUSH_JOB_HMAC_SHA_224(&state->hmac_sha_224_ooo);
    case SHA_256:
        return FLUSH_JOB_HMAC_SHA_256(&state->hmac_sha_256_ooo);
    case SHA_384:
         return FLUSH_JOB_HMAC_SHA_384(&state->hmac_sha_384_ooo);
    case SHA_512:
        return FLUSH_JOB_HMAC_SHA_512(&state->hmac_sha_512_ooo);
    case AES_XCBC:
        return FLUSH_JOB_AES_XCBC(&state->aes_xcbc_ooo);
    default: // assume MD5
        return FLUSH_JOB_HMAC_MD5(&state->hmac_md5_ooo);
    }
}


////////////////////////////////////////////////////////////////////////

JOB_AES_HMAC* 
SUBMIT_JOB(MB_MGR *state)
{
    JOB_AES_HMAC *job, *tmp;    

#ifndef LINUX
    DECLARE_ALIGNED(UINT128 xmm_save[10], 16);
    SAVE_XMMS(xmm_save);
#endif

    job = JOBS(state->next_job);	

    if ((job->hash_alg < SHA1) ||
	(job->hash_alg > MD5) ||
	(job->msg_len_to_cipher_in_bytes == 0) ||
        (job->msg_len_to_hash_in_bytes == 0) ||
        ((job->msg_len_to_cipher_in_bytes & 15) != 0) ||
        (job->auth_tag_output_len_in_bytes != auth_tag_len[job->hash_alg-1])) {
        job->status = STS_INVALID_ARGS;
    } else {

        job->status = STS_BEING_PROCESSED;

        if (job->chain_order == CIPHER_HASH) {
            // assume job->cipher_direction == ENCRYPT
            job = SUBMIT_JOB_AES_ENC(state, job);
            if (job) {
                job = SUBMIT_JOB_HASH(state, job);
                if (job && (job->chain_order == HASH_CIPHER)) {
                    SUBMIT_JOB_AES_DEC(job);
                }
            } // end if job

        } else { // job->chain_order == HASH_CIPHER
            // assume job->cipher_direction == DECRYPT
            job = SUBMIT_JOB_HASH(state, job);
            if (job && (job->chain_order == HASH_CIPHER)) {
                SUBMIT_JOB_AES_DEC(job);
            }
        }
    }

    if (state->earliest_job < 0) {
        // state was previously empty
        state->earliest_job = state->next_job;
        ADV_JOBS(state->next_job);

#ifndef LINUX
        RESTORE_XMMS(xmm_save);
#endif

        return NULL;	// if we were empty, nothing to return
    }

    ADV_JOBS(state->next_job);

    if (state->earliest_job == state->next_job) {
        // Full
        job = JOBS(state->earliest_job);
        while (job->status < STS_COMPLETED) {
            if (job->chain_order == CIPHER_HASH) {
                // assume job->cipher_direction == ENCRYPT
                tmp = FLUSH_JOB_AES_ENC(state, job);
                if (tmp) {
                    tmp = SUBMIT_JOB_HASH(state, tmp);
                } else {
                    tmp = FLUSH_JOB_HASH(state, job);
                }
                if (tmp && (tmp->chain_order == HASH_CIPHER)) {
                    SUBMIT_JOB_AES_DEC(tmp);
                }
            } else { // job->chain_order == HASH_CIPHER
                // assume job->cipher_direction == DECRYPT
                tmp = FLUSH_JOB_HASH(state, job);
                assert(tmp);
                if (tmp->chain_order == HASH_CIPHER) {
                    SUBMIT_JOB_AES_DEC(tmp);
                }
            }
        }
        ADV_JOBS(state->earliest_job);

#ifndef LINUX
        RESTORE_XMMS(xmm_save);
#endif

        return job;
    } else {
        // not full

#ifndef LINUX
        RESTORE_XMMS(xmm_save);
#endif

        job = JOBS(state->earliest_job);
        if (job->status < STS_COMPLETED)
            return NULL;
        ADV_JOBS(state->earliest_job);
        return job;
    }
}

// Replaced with "inline" version defined in mg_mgr.h using #define
/*
JOB_AES_HMAC*
get_completed_job_sse(MB_MGR *state)
{
    JOB_AES_HMAC* job;

    if (state->earliest_job < 0)
        return NULL;
    job = JOBS(state->earliest_job);
    if (job->status < STS_COMPLETED)
        return NULL;
    ADV_JOBS(state->earliest_job);
    if (state->earliest_job == state->next_job)
        state->earliest_job = -1;
    return job;
}
*/

JOB_AES_HMAC*
FLUSH_JOB(MB_MGR *state)
{
    JOB_AES_HMAC *job, *tmp;
#ifndef LINUX
    DECLARE_ALIGNED(UINT128 xmm_save[10], 16);
#endif
    UINT32 tracker = 1;

    if (state->earliest_job < 0)
        return NULL; // empty

#ifndef LINUX
    SAVE_XMMS(xmm_save);
#endif

    job = JOBS(state->earliest_job);

  
    while (job->status < STS_COMPLETED) {
        if (job->chain_order == CIPHER_HASH) {
            // assume job->cipher_direction == ENCRYPT
            tmp = FLUSH_JOB_AES_ENC(state, job);
            if (tmp) {
                tmp = SUBMIT_JOB_HASH(state, tmp);
            } else {
                tmp = FLUSH_JOB_HASH(state, job);
            }
//            assert(tmp);
            if (tmp && (tmp->chain_order == HASH_CIPHER)) {
                SUBMIT_JOB_AES_DEC(tmp);
            }
        } else { // job->chain_order == HASH_CIPHER
            // assume job->cipher_direction == DECRYPT
            tmp = FLUSH_JOB_HASH(state, job);
            assert(tmp);
  
            if (tmp->chain_order == HASH_CIPHER) {
                SUBMIT_JOB_AES_DEC(tmp);
            }
        }
    }

    ADV_JOBS(state->earliest_job);

    if (state->earliest_job == state->next_job)
        state->earliest_job = -1;

#ifndef LINUX
    RESTORE_XMMS(xmm_save);
#endif

    return job;
}

////////////////////////////////////////////////////////////////////////
/// Lower level "out of order" schedulers
////////////////////////////////////////////////////////////////////////

#ifndef AVX2
// AVX2 does not change the AES code, so the AVX2 version uses AVX code here

JOB_AES_HMAC* 
SUBMIT_JOB_AES128_DEC(JOB_AES_HMAC* job)
{
    assert((job->msg_len_to_cipher_in_bytes & 15) == 0);
    assert(job->iv_len_in_bytes == 16);
    AES_CBC_DEC_128(job->src + job->cipher_start_src_offset_in_bytes,
                    job->iv,
                    job->aes_dec_key_expanded,
                    job->dst,
                    job->msg_len_to_cipher_in_bytes);
    job->status |= STS_COMPLETED_AES;
    return (job);
}


JOB_AES_HMAC* 
SUBMIT_JOB_AES192_DEC(JOB_AES_HMAC* job)
{
    assert((job->msg_len_to_cipher_in_bytes & 15) == 0);
    assert(job->iv_len_in_bytes == 16);
    AES_CBC_DEC_192(job->src + job->cipher_start_src_offset_in_bytes,
                    job->iv,
                    job->aes_dec_key_expanded,
                    job->dst,
                    job->msg_len_to_cipher_in_bytes);
    job->status |= STS_COMPLETED_AES;
    return (job);
}
JOB_AES_HMAC* 
SUBMIT_JOB_AES256_DEC(JOB_AES_HMAC* job)
{
    assert((job->msg_len_to_cipher_in_bytes & 15) == 0);
    assert(job->iv_len_in_bytes == 16);
    AES_CBC_DEC_256(job->src + job->cipher_start_src_offset_in_bytes,
                    job->iv,
                    job->aes_dec_key_expanded,
                    job->dst,
                    job->msg_len_to_cipher_in_bytes);
    job->status |= STS_COMPLETED_AES;
    return (job);
}



JOB_AES_HMAC* 
SUBMIT_JOB_AES128_CNTR(JOB_AES_HMAC* job)
{
    assert((job->msg_len_to_cipher_in_bytes & 15) == 0);
    assert(job->iv_len_in_bytes == 16);
    AES_CNTR_128(job->src + job->cipher_start_src_offset_in_bytes,
                 job->iv,
                 job->aes_enc_key_expanded,
                 job->dst,
                 job->msg_len_to_cipher_in_bytes);
    job->status |= STS_COMPLETED_AES;
    return (job);
}

JOB_AES_HMAC* 
SUBMIT_JOB_AES192_CNTR(JOB_AES_HMAC* job)
{
    assert((job->msg_len_to_cipher_in_bytes & 15) == 0);
    assert(job->iv_len_in_bytes == 16);
    AES_CNTR_192(job->src + job->cipher_start_src_offset_in_bytes,
                 job->iv,
                 job->aes_enc_key_expanded,
                 job->dst,
                 job->msg_len_to_cipher_in_bytes);
    job->status |= STS_COMPLETED_AES;
    return (job);
}

JOB_AES_HMAC* 
SUBMIT_JOB_AES256_CNTR(JOB_AES_HMAC* job)
{
    assert((job->msg_len_to_cipher_in_bytes & 15) == 0);
    assert(job->iv_len_in_bytes == 16);
    AES_CNTR_256(job->src + job->cipher_start_src_offset_in_bytes,
                 job->iv,
                 job->aes_enc_key_expanded,
                 job->dst,
                 job->msg_len_to_cipher_in_bytes);
    job->status |= STS_COMPLETED_AES;
    return (job);
}

#endif

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

UINT32 
QUEUE_SIZE(MB_MGR *state)
{
    int a, b;
    if (state->earliest_job < 0)
        return 0;
    a = state->next_job / sizeof(JOB_AES_HMAC);
    b = state->earliest_job / sizeof(JOB_AES_HMAC);
    return ((a-b) & (MAX_JOBS-1));
    //    return ((((signed int)(state->next_job - state->earliest_job))/sizeof(JOB_AES_HMAC)) & (MAX_JOBS-1));
}

