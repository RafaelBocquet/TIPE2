LHS_FILES = Main.lhs Term.lhs 
TEX_FILES = presentation.tex # $(LHS_FILES:.lhs=.tex)
MAIN_TEX_FILE = presentation.tex

SRC_DIR = ../src
BUILD_DIR = build

all: presentation.pdf

dvi: $(TEX_FILES)
	@echo $(TEX_FILES)
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR) && latex -shell-escape ../presentation.tex
	cd $(BUILD_DIR) && cp ../presentation.bib . && bibtex presentation
	cd $(BUILD_DIR) && latex -shell-escape ../presentation.tex

presentation.pdf: $(TEX_FILES)
	@echo $(TEX_FILES)
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR) && latex -shell-escape ../presentation.tex
	cd $(BUILD_DIR) && cp ../presentation.bib . && bibtex presentation
	cd $(BUILD_DIR) && latex -shell-escape ../presentation.tex
	cd $(BUILD_DIR) && dvips presentation.dvi
	cd $(BUILD_DIR) && ps2pdf presentation.ps
	cp $(BUILD_DIR)/presentation.pdf .

clean:
	$(RM) -r $(BUILD_DIR)
	$(RM) presentation.pdf