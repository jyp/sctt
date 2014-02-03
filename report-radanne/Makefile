
mainTest: Report.pdf

%-delayed.mp: %.mp
	rm -f $@
	mpost $<
	mpost $<

%.pdf: %.tex %-delayed.mp
	pdflatex $<
	bibtex $(basename $<).aux
	pdflatex $<
	pdflatex $<

%.mp %.tex: %.hs
	ghc -i../src/ --make $<
	./$*

%.hspp: %.hs
	ghc -E $<
