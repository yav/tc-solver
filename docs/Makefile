
.PHONY: default clean

default: note.html note.pdf


BUILD=build


%.html: %.md
	pandoc --to=html --standalone --toc -o $@ $<


%.tex: %.md
	pandoc --to=latex --standalone --toc -o $@ $<


%.pdf: %.tex
	mkdir $(BUILD)
	pdflatex --output-directory $(BUILD) $<
	cp $(BUILD)/$@ $@

clean:
	rm -rf build
