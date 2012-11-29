SHELL=bash

all: core.cmo core.cmx main.native main_gen.native # main_gen.bytecode 

FORCE:


 # external dependencies
OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep

LIBS=str unix threads  
OBJS= # core cf pr # common encode2 message file queue3

INCLUDES=-I +threads  # all relevant -I options here
OCAMLFLAGS=$(INCLUDES) $(LIBS:=.cma) # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) $(LIBS:=.cmxa) # add other options for ocamlopt here

 ################################################################################
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

%.bytecode: %.ml $(OBJS:=.cmo)
	$(OCAMLC) -o $*.bytecode $(OCAMLFLAGS) $(INCLUDES) $(OBJS:=.cmo) $*.ml 

%.native: %.ml $(OBJS:=.cmx)
	$(OCAMLOPT) -o $*.native $(OCAMLOPTFLAGS) $(INCLUDES) $(OBJS:=.cmx) $*.ml 


 ################################################################################
clean: FORCE
	rm -f {main,main_gen}.{native,bytecode}
	rm -f *.cm[iox]
	rm -f *.o
	rm -f *.tmp # log files, stop.tmp
	rm -f tmp.native tmp.ml

