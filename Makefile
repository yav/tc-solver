.PHONY: run doc clean

run: TcTypeNatsRules.hs
	runhaskell UI.hs

doc: TcTypeNatsRules.hs doc/Notes.pdf
	haddock -html -o html-haddock Test.hs

doc/Notes.pdf: Notes.lhs
	mkdir -p doc
	pdflatex --output-directory=doc Notes.lhs

TcTypeNatsRules.hs: ./genRule.lhs
	runhaskell $< > $@

.PHONY: api
api: api/UI.html

api/%.html: %.hs
	mkdir -p api
	haddock --html -o api $<

clean:
	rm -rf TcTypeNatsRules.hs doc html-haddock

