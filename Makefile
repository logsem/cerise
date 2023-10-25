# Is CI_EXAMPLES used in any place ?
CI_EXAMPLES    :=    theories/examples/buffer.v \
					 theories/examples/minimal_counter.v \
					 theories/examples/counter/counter_adequacy.v \
					 theories/examples/adder_adequacy.v \
					 theories/examples/counter_binary/counter_binary.v \
					 theories/examples/counter_binary/counter_binary_preamble.v \
					 theories/examples/lse.v \
					 theories/examples/dynamic_sealing.v \
					 theories/examples/ocpl_lowval_like.v

FUNDAMENTAL		:=	 theories/fundamental.v
COQMAKEFILE 	?=   Makefile.coq
COQ_PROJ 		?= _CoqProject

all: $(COQMAKEFILE)
		+@$(MAKE) -f $^ $@

# Forward `make` commands to `$(COQMAKEFILE)`
%: $(COQMAKEFILE)
		+@$(MAKE) -f $^ $@

fundamental: export TGTS=${FUNDAMENTAL:.v=.vo}
fundamental: $(COQMAKEFILE) only

$(COQMAKEFILE): $(COQ_PROJ)
		coq_makefile -f $^ -o $@

.PHONY: all fundamental ci

# Thanks to Vincent Lafeychine for the help to refactor the Makefile
