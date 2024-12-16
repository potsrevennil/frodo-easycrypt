.phony: pdf clean

LATEXMK ?= latexmk
LMKFLAGS ?= -pdf

TEXTFILES = $(wildcard *.tex)
ROOT_TEXTFILE = main.tex

pdf: $(TEXTFILES)
	$(LATEXMK) $(LMKFLAGS) -pvc $(ROOT_TEXTFILE)

clean:
	$(LATEXMK) -C
