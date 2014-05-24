LHS_FILES = Main.lhs

all: presentation.pdf

_presentation.tex: presentation.tex ../src/Main.lhs
	lhs2TeX --poly presentation.tex -o _presentation.tex

presentation.pdf: _presentation.tex
	pdflatex _presentation.tex

clean:
	rm _presentation.*