# -*- Makefile -*-

# --------------------------------------------------------------------
AS      ?= as
CC      ?= gcc
CFLAGS  ?= -Wall -Wno-unused-function -Ofast
CI      ?= 0
export CI
EXCLUDE ?=

# --------------------------------------------------------------------
SRC      := ../src
BIN      ?= bin
COMMON   := common
EXT      := ../ext
RANDLIB  ?= $(EXT)/randombytes/librandombytes.a
SSBD_DIR := $(EXT)/ssbd-tools

JAZZ    ?= $(filter-out $(addprefix $(SRC)/,$(EXCLUDE)), $(sort $(dir $(shell find $(SRC) -name '*.jazz'))))
BENCH   := $(subst $(SRC),$(BIN), $(JAZZ))
BENCHS  := $(addsuffix bench, $(BENCH))

# --------------------------------------------------------------------

RDIR        = $(subst $(BIN)/,,$(@D))
OPERATION   = $(subst crypto_,,$(word 1, $(subst /, ,$(RDIR))))
OPERATION1  = $(shell echo $(OPERATION) | tr a-z A-Z)
NAMESPACE0  = $(subst crypto_$(OPERATION)_,,$(subst -,_,$(subst /,_,$(RDIR))))
NAMESPACE   = jade_$(OPERATION)_$(NAMESPACE0)
NAMESPACE1  = JADE_$(OPERATION1)_$(NAMESPACE0)
IDIR        = $(subst $(BIN),$(SRC),$(@D))
ASM         = $(IDIR)/$(OPERATION).s

MAIN        = $(COMMON)/crypto_$(OPERATION).c
DEFINE     ?=
DNAMESPACES = -DJADE_NAMESPACE=$(NAMESPACE1) -DJADE_NAMESPACE_LC=$(NAMESPACE)
INCLUDES    = -I$(IDIR)/include/ -I$(COMMON)/ -I$(EXT)/randombytes/
COMPILE     = $(CC) $(CFLAGS) -o $@ $(DEFINE) $(DNAMESPACES) $(INCLUDES) $(MAIN) $(ASM) $(RANDLIB)

# --------------------------------------------------------------------
.PHONY: __phony benchs

default: benchs

benchs: $(BENCHS)

$(BENCHS):
%/bench: $(RANDLIB) __phony | %/
	$(MAKE) -C $(IDIR) || true
	$(COMPILE) || true

$(RANDLIB):
	$(MAKE) -C $(@D)

$(BENCH): ; @mkdir -p $@

run: benchs
	for d in $(BENCH); do (cd $$d && ./bench); done

# --------------------------------------------------------------------
.PHONY: ssbd-tools
ssbd-tools:
	make -C $(SSBD_DIR)

# --------------------------------------------------------------------
clean:
	rm -fr $(BIN)

