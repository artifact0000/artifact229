
default: main.pdf

all:
	./scripts/step1_extract_data_from_raw
	./scripts/step2_preprocess_tables_paper
	./scripts/step3_preprocess_tables_ssbd_rsb
	./scripts/step4_tables_codesize
	$(MAKE) main.pdf

main.pdf: main.tex tables_paper.tex tables_ssbd_rsb.tex tables_codesize.tex
	pdflatex main.tex
	pdflatex main.tex

clean:
	rm -f main.aux main.log main.out main.toc

distclean: clean
	rm -f main.pdf
