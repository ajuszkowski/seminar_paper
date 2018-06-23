.PHONY: all once clean

TEXFILE=cs-seminar
OUTPUT=out

all: clean once biber once-2 once-3 #convert check
	# all: OK

clean:
	#rmdir --ignore-fail-on-non-empty $(OUTPUT)
	rm -rvf $(OUTPUT)/*
	mkdir -p $(OUTPUT)
	# clean: OK

once once-2 once-3:
	pdflatex --output-directory=$(OUTPUT) "\def\IsAalto{1} \input{$(TEXFILE)}"
	# once: OK

biber:
	#biber $(TEXFILE) --output-directory=$(OUTPUT) #--quiet
	bibtex $(OUTPUT)/$(TEXFILE)
	# biber: OK
