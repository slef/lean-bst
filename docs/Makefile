.PHONY: all snippets clean
all: build/main.pdf

snippets: ../RotationBST.lean extract_snippets.py
	python3 extract_snippets.py

main.tex: main.texlish
	texlish main.texlish

build/main.pdf: main.tex snippets
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex

clean:
	rm -rf build main.tex
