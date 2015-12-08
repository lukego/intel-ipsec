LIB=libIPSec_MB.a
YASM=/nfs/site/disks/iots4/engineering/cai_isa/tools/yasm-bdw/yasm
OBJ_DIR=obj
INCLUDE_DIRS := include . 

INCLUDES := $(foreach i,$(INCLUDE_DIRS),-I $i)

CXX := g++
CC  := gcc
CXXFLAGS := -g -D LINUX -D NDEBUG $(INCLUDES) -O2
ASMFLAGS := -f x64 -f elf64 -X gnu -g dwarf2 -D LINUX -D __linux__ $(INCLUDES)
LDFLAGS += -g

lib_objs := \
	aes128_cbc_dec_by4_sse.o \
	aes128_cbc_dec_by8_avx.o \
	aes128_cntr_by4_sse.o \
	aes128_cntr_by8_avx.o \
	aes128_ecbenc_x3.o \
	aes192_cbc_dec_by4_sse.o \
	aes192_cbc_dec_by8_avx.o \
	aes192_cntr_by4_sse.o \
	aes192_cntr_by8_avx.o \
	aes256_cbc_dec_by4_sse.o \
	aes256_cbc_dec_by8_avx.o \
	aes256_cntr_by4_sse.o \
	aes256_cntr_by8_avx.o \
	aes_cbc_enc_128_x4.o \
	aes_cbc_enc_128_x8.o \
	aes_cbc_enc_192_x4.o \
	aes_cbc_enc_192_x8.o \
	aes_cbc_enc_256_x4.o \
	aes_cbc_enc_256_x8.o \
	aes_keyexp_128.o \
	aes_keyexp_192.o \
	aes_keyexp_256.o \
	aes_xcbc_mac_128_x4.o \
	aes_xcbc_mac_128_x8.o \
	mb_mgr_aes192_flush_avx.o \
	mb_mgr_aes192_flush_sse.o \
	mb_mgr_aes192_submit_avx.o \
	mb_mgr_aes192_submit_sse.o \
	mb_mgr_aes256_flush_avx.o \
	mb_mgr_aes256_flush_sse.o \
	mb_mgr_aes256_submit_avx.o \
	mb_mgr_aes256_submit_sse.o \
	mb_mgr_aes_flush_avx.o \
	mb_mgr_aes_flush_sse.o \
	mb_mgr_aes_submit_avx.o \
	mb_mgr_aes_submit_sse.o \
	mb_mgr_aes_xcbc_flush_avx.o \
	mb_mgr_aes_xcbc_flush_sse.o \
	mb_mgr_aes_xcbc_submit_avx.o \
	mb_mgr_aes_xcbc_submit_sse.o \
	mb_mgr_hmac_flush_avx.o \
	mb_mgr_hmac_flush_avx2.o \
	mb_mgr_hmac_flush_sse.o \
	mb_mgr_hmac_md5_flush_avx.o \
	mb_mgr_hmac_md5_flush_avx2.o \
	mb_mgr_hmac_md5_flush_sse.o \
	mb_mgr_hmac_md5_submit_avx.o \
	mb_mgr_hmac_md5_submit_avx2.o \
	mb_mgr_hmac_md5_submit_sse.o \
	mb_mgr_hmac_sha_224_flush_avx.o \
	mb_mgr_hmac_sha_224_flush_avx2.o \
	mb_mgr_hmac_sha_224_flush_sse.o \
	mb_mgr_hmac_sha_224_submit_avx.o \
	mb_mgr_hmac_sha_224_submit_avx2.o \
	mb_mgr_hmac_sha_224_submit_sse.o \
	mb_mgr_hmac_sha_256_flush_avx.o \
	mb_mgr_hmac_sha_256_flush_avx2.o \
	mb_mgr_hmac_sha_256_flush_sse.o \
	mb_mgr_hmac_sha_256_submit_avx.o \
	mb_mgr_hmac_sha_256_submit_avx2.o \
	mb_mgr_hmac_sha_256_submit_sse.o \
	mb_mgr_hmac_sha_384_flush_avx.o \
	mb_mgr_hmac_sha_384_flush_avx2.o \
	mb_mgr_hmac_sha_384_flush_sse.o \
	mb_mgr_hmac_sha_384_submit_avx.o \
	mb_mgr_hmac_sha_384_submit_avx2.o \
	mb_mgr_hmac_sha_384_submit_sse.o \
	mb_mgr_hmac_sha_512_flush_avx.o \
	mb_mgr_hmac_sha_512_flush_avx2.o \
	mb_mgr_hmac_sha_512_flush_sse.o \
	mb_mgr_hmac_sha_512_submit_avx.o \
	mb_mgr_hmac_sha_512_submit_avx2.o \
	mb_mgr_hmac_sha_512_submit_sse.o \
	mb_mgr_hmac_submit_avx.o \
	mb_mgr_hmac_submit_avx2.o \
	mb_mgr_hmac_submit_sse.o \
	md5_x4x2_avx.o \
	md5_x4x2_sse.o \
	md5_x8x2_avx2.o \
	save_xmms.o \
	sha1_mult_avx.o \
	sha1_mult_sse.o \
	sha1_one_block_avx.o \
	sha1_one_block_sse.o \
	sha1_x8_avx2.o \
	sha224_one_block_avx.o \
	sha224_one_block_sse.o \
	sha256_oct_avx2.o \
	sha256_one_block_avx.o \
	sha256_one_block_sse.o \
	sha384_one_block_avx.o \
	sha384_one_block_sse.o \
	sha512_one_block_avx.o \
	sha512_one_block_sse.o \
	sha512_x2_avx.o \
	sha512_x2_sse.o \
	sha512_x4_avx2.o \
	sha_256_mult_avx.o \
	sha_256_mult_sse.o \
	\
	aes_xcbc_expand_key.o \
	mb_mgr_avx.o \
	mb_mgr_avx2.o \
	mb_mgr_sse.o \
	md5_one_block.o

gcm_objs := gcm_sse.o gcm_avx_gen2.o gcm_avx_gen4.o


obj2_files := $(lib_objs:%=$(OBJ_DIR)/%) $(gcm_objs:%=$(OBJ_DIR)/%)

.PHONY: lib clean

all: lib

lib: $(LIB)

$(LIB): $(obj2_files)
	ar -qcs $@ $^

$(obj2_files): | $(OBJ_DIR)

$(OBJ_DIR)/%.o:%.cpp
	@ echo "Making object file $@ "
	$(CXX) -c $(CXXFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:%.c
	@ echo "Making object file $@ "
	$(CC) -c $(CXXFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:%.asm
	@ echo "Making object file $@ "
	$(YASM) $(ASMFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:sse/%.cpp
	@ echo "Making object file $@ "
	$(CXX) -c $(CXXFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:sse/%.c
	@ echo "Making object file $@ "
	$(CC) -c $(CXXFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:sse/%.asm
	@ echo "Making object file $@ "
	$(YASM) $(ASMFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:avx/%.cpp
	@ echo "Making object file $@ "
	$(CXX) -c $(CXXFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:avx/%.c
	@ echo "Making object file $@ "
	$(CC) -c $(CXXFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:avx/%.asm
	@ echo "Making object file $@ "
	$(YASM) $(ASMFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:avx2/%.cpp
	@ echo "Making object file $@ "
	$(CXX) -c $(CXXFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:avx2/%.c
	@ echo "Making object file $@ "
	$(CC) -c $(CXXFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:avx2/%.asm
	@ echo "Making object file $@ "
	$(YASM) $(ASMFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR)/%.o:include/%.asm
	@ echo "Making object file $@ "
	$(YASM) $(ASMFLAGS) $< -o $@
	@ echo "--------------------------------------------------------------"

$(OBJ_DIR):
	mkdir $(OBJ_DIR)

clean:
	rm -Rf $(obj2_files)
	rm -Rf $(LIB)

