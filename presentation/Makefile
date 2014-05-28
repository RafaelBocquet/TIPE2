LHS_FILES = Main.lhs

all: presentation.pdf

presentation.pdf: presentation.tex
	mkdir -p build
	cd build && latex -shell-escape ../presentation.tex
	cd build && latex -shell-escape ../presentation.tex
	cd build && dvipdf presentation.dvi ../presentation.pdf

clean:
	$(RM) -r build
	$(RM) presentation.pdf