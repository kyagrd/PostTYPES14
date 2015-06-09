.PHONY: all pdf ps dvi clean_backup

HSSRC=PHOASshow.hs PHOASeval.hs \
      HOASshow.hs HOASeval.hs HOASevalV.hs Exp2Expr.hs Len.hs

TEXSRC=main.tex intro.tex mendler.tex eval.tex murec.tex theory.tex \
       related.tex ongoing.tex summary.tex

## all: pdf

pdf: main.pdf

ps: main.ps

dvi: main.dvi

clean_backup:
	-rm *.*~ *~

main.pdf: ${TEXSRC} $(HSSRC) main.bbl
	pdflatex main

main.dvi: ${TEXSRC} $(HSSRC) main.bbl
	latex main

main.ps: main.dvi
	dvips main

main.aux:
	latex main

main.bbl: main.aux main.bib
	bibtex main
	latex main

