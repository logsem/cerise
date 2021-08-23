EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'https://plv.mpi-sws.org/coqdoc/iris/' iris \
  --external 'https://plv.mpi-sws.org/coqdoc/stdpp/' stdpp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

CI_EXAMPLES:="\
  theories/examples/buffer.vo \
  theories/examples/minimal_counter.vo \
  theories/examples/counter_adequacy.vo \
  theories/examples/adder_adequacy.vo \
  theories/examples/counter_binary.vo \
  theories/examples/counter_binary_preamble.vo \
  theories/examples/lse.vo \
	theories/examples/dynamic_sealing.vo \
	theories/examples/ocpl_lowval_like.vo"

.PHONY: all coq clean html
all: coq

fundamental: Makefile.coq
	$(MAKE) -f Makefile.coq pretty-timed only TGTS="theories/fundamental.vo"

coq: Makefile.coq
	$(MAKE) -f Makefile.coq pretty-timed

html: Makefile.coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cp $(EXTRA_DIR)/resources/* html

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coq.conf:
	coq_makefile -f _CoqProject -o Makefile.coq

include Makefile.coq.conf

skip-qed: Makefile.coq.conf
	./disable-qed.sh $(COQMF_VFILES)

ci: skip-qed
	$(MAKE) -f Makefile.coq pretty-timed TGTS=$(CI_EXAMPLES)

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf html
