SHELL=bash

OCAMLOPT=ocamlopt

BASEDIR=../../ocaml/modular_ocaml
MAINGEN=$(BASEDIR)/main_gen.native
CORE=$(BASEDIR)/core.cmx

test: bnf.native bnf2.native
	./bnf2.native -f bnf.g

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
	rm -f {bnf,bnf2}.{cmi,cmx,ml,o,native}


.PRECIOUS: %.ml

FORCE: