# COQTOP must be set 
# COQTOP =

RM=/bin/rm -f

# This is hand-written Makefile!
# Derived paths

COQMKTOP = $(COQTOP)/bin/coqmktop
COQC = $(COQTOP)/bin/coqc
CAMLP4O = "camlp4o -I $(COQTOP)  pa_extend.cmo pa_extend_m.cmo q_MLast.cmo  parsing/grammar.cma -impl"

# includes : cut/past from coq Makefile
# camlp4o  : idem - no idea about what it is doing
INCLUDES = \
	-I $(COQTOP)/config -I $(COQTOP)/tools -I $(COQTOP)/tools/coqdoc -I $(COQTOP)/scripts -I $(COQTOP)/lib -I $(COQTOP)/kernel \
	-I $(COQTOP)/library -I $(COQTOP)/proofs -I $(COQTOP)/tactics -I $(COQTOP)/pretyping -I $(COQTOP)/interp -I $(COQTOP)/toplevel \
	-I $(COQTOP)/parsing -I $(COQTOP)/ide/utils -I $(COQTOP)/ide -I $(COQTOP)/translate  -I $(COQTOP)/contrib/interface  -I $(COQTOP)/contrib/ring

define coqc 
	@echo coqc $(1)
	@$(COQC) $(1)
endef


define ocamlcomp
	@echo ocamlcomp $(1)
	@ocamlopt  -c -dtypes $(INCLUDES) -I '+camlp4' -pp $(CAMLP4O)  -impl $(1)
	@ocamlc -g   -c -dtypes $(INCLUDES) -I '+camlp4' -pp $(CAMLP4O) -impl $(1)
endef

define mktop
	@echo coqmktop $(1)
	@$(COQMKTOP) $(1)
endef

all : 
ifdef COQTOP
	$(MAKE) world
else
	@echo COQTOP is undefined : set COQTOP to the coq distribution directory
endif

world :  micromega micromega.opt Micromegatac.vo

# the coq part
tacticsPerso.vo : tacticsPerso.v
	$(call coqc,tacticsPerso.v)

Util.vo : Util.v tacticsPerso.vo
	$(call coqc,Util.v)

Refl.vo : Util.vo Refl.v
	$(call coqc,Refl.v)

Micromega.vo micromega.ml micromega.mli: Util.vo Refl.vo Micromega.v
	$(call coqc,Micromega.v)

micromega.cmi : micromega.mli
	ocamlc -g  -c -dtypes micromega.mli

# Extracted code
micromega.cmo micromega.cmx: micromega.ml micromega.cmi
	$(call ocamlcomp, micromega.ml)

utils.cmx utils.cmo : utils.ml micromega.cmx
	$(call ocamlcomp, utils.ml)


g_micromega.cmx g_micromega.cmo: g_micromega.ml4 coq_micromega.cmx
	$(call ocamlcomp, g_micromega.ml4)


certificate.cmx : micromega.cmx utils.cmx fourier_num.cmx certificate.ml
	$(call ocamlcomp, certificate.ml)


coq_micromega.cmx coq_micromega.cmo : coq_micromega.ml micromega.cmx utils.cmx certificate.cmx
	$(call ocamlcomp, coq_micromega.ml)

micromega.cmxa micromega.cma: coq_micromega.cmx g_micromega.cmx micromega.cmx utils.cmx  fourier_num.cmx certificate.cmx
	@ocamlopt -a -o micromega.cmxa   utils.cmx fourier_num.cmx micromega.cmx certificate.cmx     coq_micromega.cmx  g_micromega.cmx  
	@ocamlc -g  -a -o micromega.cma   utils.cmo fourier_num.cmo micromega.cmo certificate.cmo     coq_micromega.cmo  g_micromega.cmo  
	@echo ocamllib -a -o micromega   utils micromega  fourier_num coq_micromega  g_micromega  

fourier_num.cmx fourier_num.cmo : fourier_num.ml
	$(call ocamlcomp, fourier_num.ml)



micromega.opt : micromega.cmxa
	$(call mktop,-opt -o micromega.opt  nums.cmxa micromega.cmxa)

micromega : micromega.cma
	$(call mktop, -o micromega nums.cma micromega.cma)

Micromegatac.vo : Micromegatac.v micromega
	./micromega -compile Micromegatac

.PHONY: clean

clean:
	$(RM) *~ *.o *.vo *.cm[iaxo] *.cmxa micromega micromega.opt micromega.ml micromega.mli *.annot