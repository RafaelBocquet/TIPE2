LHS_FILES = Main.lhs
TEX_FILES = presentation.tex # $(LHS_FILES:.lhs=.tex)
MAIN_TEX_FILE = presentation.tex

SRC_DIR = ../src
BUILD_DIR = build

all: presentation.pdf

presentation.pdf: $(TEX_FILES)
	@echo $(TEX_FILES)
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR) && latex -shell-escape ../presentation.tex ../graph.tex
	cd $(BUILD_DIR) && latex -shell-escape ../presentation.tex ../graph.tex
	cd $(BUILD_DIR) && dvipdf presentation.dvi ../presentation.pdf

clean:
	$(RM) -r $(BUILD_DIR)
	$(RM) presentation.pdf