.PHONY: all snippets clean
all: build/main.pdf build/state-elimination.pdf

snippets: ../RotationBST.lean ../StateElimination.lean ../PeriodicProbe.lean extract_snippets.py
	python3 extract_snippets.py

main.tex: main.texlish
	texlish main.texlish

build/main.pdf: main.tex snippets
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex

clean:
	rm -rf build main.tex state-elimination.tex

state-elimination.tex: state-elimination.texlish
	texlish state-elimination.texlish

build/state-elimination.pdf: state-elimination.tex snippets
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build state-elimination.tex
