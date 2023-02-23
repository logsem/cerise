.PHONY: all clean interpreter
all: interpreter

interpreter:
	$(MAKE) -C interpreter

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf html
