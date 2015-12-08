INCLUDE_DIRS := ../include ..

INCLUDES := $(foreach i,$(INCLUDE_DIRS),-I $i)

CC  := gcc
CXXFLAGS := -g -D LINUX $(INCLUDES)
LDFLAGS += -g

ipsec_MB_testapp: main.o
	$(CC) $(LDFLAGS) -o $@ main.o ../libIPSec_MB.a

main.o: main.c do_test.h
	$(CC) $(CXXFLAGS) -c $< -o $@

