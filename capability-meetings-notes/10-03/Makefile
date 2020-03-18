OPTS=-latexoption=-shell-escape

all:
	latexmk $(OPTS) -pdf main

loop:
	latexmk $(OPTS) -pdf -pvc main

clean::
	rm -rf `cat .gitignore`

.PHONY: all loop clean
