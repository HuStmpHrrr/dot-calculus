ALL_TEX := $(shell find . -path .git -prune -o -type f -name '*.tex')
ALL_DIR := $(shell find . -path .git -prune -o -type f -name '*.tex' -printf "%h\n" | uniq)
TARGETS := $(basename ${ALL_TEX})

ALL_PDF := $(addsuffix .pdf, ${TARGETS})

.phony: all clean clean_pdf clean_aux clean_log list ${ALL_DIR}

all: ${ALL_PDF}

prep/writeup.pdf: prep/ref.bib

${ALL_PDF} : %.pdf : %.tex
	pdflatex --output-directory=$(dir $@) $<
	biber --output-directory $(dir $@) $(notdir $(basename $<))
	pdflatex --output-directory=$(dir $@) $<

define search_pdf
$(1) : $(shell find $(1) -type f -name '*.tex' | sed 's/tex$$/pdf/')
endef

$(foreach dir, $(ALL_DIR), $(eval $(call search_pdf, ${dir})))

list:
	@make -rpn | sed -n -e '/^$$/ { n ; /^[^ .#][^ ]*:/p ; }'

clean: clean_pdf clean_aux clean_log clean_toc clean_out clean_nav clean_snm
	-find . -path .git -prune -o -type f -name '*~' -exec rm {} +

clean_pdf:
	-rm ${ALL_PDF}

clean_aux:
	-rm $(addsuffix .aux, ${TARGETS})

clean_log:
	-rm $(addsuffix .log, ${TARGETS})

clean_toc:
	-rm $(addsuffix .toc, ${TARGETS})

clean_out:
	-rm $(addsuffix .out, ${TARGETS})

clean_nav:
	-rm $(addsuffix .nav, ${TARGETS})

clean_snm:
	-rm $(addsuffix .snm, ${TARGETS})
