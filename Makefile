DIRS=src extraction from_compcert

INCLUDES=$(patsubst %,-I %, $(DIRS))

COQLIBS:=-I ~/formal/cases/src -R ~/formal/cases/theories Case_Tactics\
	-R ~/formal/PilkiLib "" -R src/ "" -R from_compcert ""


COQC=coqc -q $(INCLUDES) $(COQLIBS)
COQDEP=coqdep $(COQLIBS)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) $(COQLIBS) -batch -load-vernac-source


OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
  -I extraction -I driver

VPATH=$(DIRS)
GPATH=$(DIRS)

FCPCERT= Axioms.v  Errors.v Integers.v  Floats.v  AST.v    Maps.v \
  Memdata.v   Values.v Memtype.v CompMemory.v 
#   Events.v Intv.v  Globalenvs.v  Cminor.v \
  Smallstep.v Ordered.v Switch.v
#  RTL.v RTLgen.v CminorSel.v Op.v Registers.v RTLgenspec.v Sets.v \
#  RTLgenproof.v

SRC= CeildFloord.v ArithClasses.v Coqlib.v Coqlibext.v ClassesAndNotations.v Do_notation.v Libs.v Memory.v  ArithClasses.v \
  PolyBase.v  Bounds.v  Polyhedra.v BoxedPolyhedra.v Instructions.v TimeStamp.v  Loops.v PLang.v\
  PDep.v \
   ExtractPoly.v  Tilling.v PermutInstrs.v Final.v\
  SimpleLanguage.v OCamlInterface.v
# Coqlib.v Coqlibext.v Do_notation.v 

EXTRACTION=extraction.v

FILES=$(FCPCERT) $(SRC) $(EXTRACTION) 
PFILES=$(addprefix from_compcert/,$(FCPCERT)) $(addprefix src/,$(SRC)) $(addprefix extraction/,$(EXTRACTION)) 

validator: driver/*.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) PrintingPprog.native

proof: $(PFILES:.v=.vo)


extraction: extraction.v
	rm -f extraction/*.ml extraction/*.mli extraction/*.vo
	$(COQEXEC) extraction/extraction.v

.PHONY: extraction

.SUFFIXES: .v .vo

.v.vo: $(PFILES)
#	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob /dev/null $*.v

depend: $(PFILES)
	$(COQDEP) $^ \
        > .depend


clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -rf _build
	rm -f doc/coq2html.ml doc/coq2html
	rm -f extraction/*.ml extraction/*.mli



# include .depend

FORCE:
