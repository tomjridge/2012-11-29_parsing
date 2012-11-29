SHELL=bash

OCAMLOPT=ocamlopt

BASEDIR=../../src
MAINGEN=$(BASEDIR)/main_gen.native
CORE=$(BASEDIR)/core.cmx

test: arith.native length.native ml.native # xmlprsr.native # bracket.native
	./arith.native -f arith.txt
	./length.native -f length.txt
	./ml.native -f ml.txt

#	./xmlprsr.native -f xmlprsr.xml
#	./bracket.native -f bracket.txt
#	./ml.native -f ml.txt

%.native: %.ml
	$(OCAMLOPT) -o $@ -I $(BASEDIR) $(CORE) $<

%.ml: %.g $(MAINGEN)
	$(MAINGEN) -basedir $(BASEDIR) -g $< >$*.ml

$(MAINGEN):
	echo "Please build $@ first."
	false

$(CORE):
	echo "Please build $@ first."
	false

clean: FORCE
	rm -f {arith,bracket,length,ml,xmlprsr}.{cmi,cmx,ml,o,native}


.PRECIOUS: %.ml

FORCE: