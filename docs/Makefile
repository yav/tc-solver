
.PHONY: default

default: note.html


%.html: %.txt
	pandoc --to=html --standalone --toc -o $@ $<


%.tex: %.txt
	pandoc --to=latex --standalone --toc -o $@ $<


%.pdf: %.tex
	pdflatex $<


