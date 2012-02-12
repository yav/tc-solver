
.PHONY: default clean

default: note.html note.pdf evidence.pdf evidence.html axioms.pdf axioms.html \
         eval.html eval.pdf


BUILD=build


%.html: %.md
	pandoc --to=html --standalone --toc -o $@ $<


%.tex: %.md
	pandoc --to=latex --standalone --toc -o $@ $<


%.pdf: %.tex
	mkdir -p $(BUILD)
	pdflatex --output-directory $(BUILD) $<
	pdflatex --output-directory $(BUILD) $<
	cp $(BUILD)/$@ $@

clean:
	rm -rf build *.pdf *.html
