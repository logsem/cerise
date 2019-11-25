# Usually, only these lines need changing
TEXFILE=paper
BIBFILES:=$(wildcard *.bib)
INPUTFILES:=$(wildcard *.tex) $(wildcard *.sty)

OUT:=.out
BACKLINK:=$(OUT)/$(TEXFILE).pdf

all: $(TEXFILE).pdf

$(BACKLINK):
	mkdir -p $(OUT)
	rm -f $(BACKLINK)
	ln -s '../$(TEXFILE).pdf' $(BACKLINK)

# Compile main tex file
$(TEXFILE).pdf: $(TEXFILE).tex $(BIBFILES) $(BACKLINK) $(INPUTFILES)
	latexmk -pdf -output-directory=$(OUT) -interaction=nonstopmode $(TEXFILE)

# Clean up stray files
clean:
	latexmk -c
	rm -rf $(TEXFILE).pdf
	rm -rf $(OUT)

.PHONY: all clean
