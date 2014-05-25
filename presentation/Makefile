LHS_FILES = Main.lhs

all: presentation.pdf

presentation.pdf: presentation.tex
	mkdir build
	latex -shell-escape --output-directory=build presentation.tex
	latex -shell-escape --output-directory=build presentation.tex
	dvipdf presentation.dvi

clean:
	$(RM) -r build
	$(RM) presentation.pdf