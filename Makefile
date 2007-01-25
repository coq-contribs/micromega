# COQTOP must be set 
# COQTOP =
##START

COQMKTOP = $(COQTOP)/bin/coqmktop -I `ocamlc -where`/camlp4

COQC = $(COQTOP)/bin/coqc

# Petit hack pour contourner le fait que sous FreeBSD, camlp4o est en fait ocamlp4o.opt...
ARCH = $(shell uname -s)
ifeq ($(ARCH),FreeBSD)
  CAMLP4O = "camlp4o.byte -I $(COQTOP)  pa_extend.cmo pa_extend_m.cmo q_MLast.cmo  parsing/grammar.cma -impl"
else
  CAMLP4O = "camlp4o -I $(COQTOP)  pa_extend.cmo pa_extend_m.cmo q_MLast.cmo  parsing/grammar.cma -impl"
endif

# includes : cut/past from coq Makefile
# camlp4o  : idem - no idea about what it is doing
INCLUDES = \
	-I $(COQTOP)/config -I $(COQTOP)/tools -I $(COQTOP)/tools/coqdoc -I $(COQTOP)/scripts -I $(COQTOP)/lib -I $(COQTOP)/kernel \
	-I $(COQTOP)/library -I $(COQTOP)/proofs -I $(COQTOP)/tactics -I $(COQTOP)/pretyping -I $(COQTOP)/interp -I $(COQTOP)/toplevel \
	-I $(COQTOP)/parsing -I $(COQTOP)/ide/utils -I $(COQTOP)/ide -I $(COQTOP)/translate  -I $(COQTOP)/contrib/interface -I $(COQTOP)/contrib/ring

define coqc 
	@echo coqc $(1)
	@$(COQC) $(1)
endef


define ocamlp4
	@echo ocamlp4 $(1)
	@ocamlopt  -c -dtypes $(INCLUDES) -I '+camlp4' -pp $(CAMLP4O)  -impl $(1)
endef
#	@ocamlc -g   -c -dtypes $(INCLUDES) -I '+camlp4' -pp $(CAMLP4O) -impl $(1)


define ocamlcomp
	@echo ocamlcomp $(1)
	@ocamlopt  -c -dtypes $(INCLUDES)  $(1)
endef
#	@ocamlc -g   -c -dtypes $(INCLUDES)  $(1)



define mktop
	@echo coqmktop $(1)
	@$(COQMKTOP) $(1)
endef

all : 
ifdef COQTOP
	echo $(ARCH)
	${MAKE} world
else
	@echo COQTOP is undefined : set COQTOP to the coq distribution directory
endif

world :   micromega.opt Micromegatac.vo

# the coq part
tacticsPerso.vo : tacticsPerso.v
	$(call coqc,tacticsPerso.v)

Util.vo : Util.v tacticsPerso.vo
	$(call coqc,Util.v)

Refl.vo : Util.vo Refl.v
	$(call coqc,Refl.v)

CheckerMaker.vo : CheckerMaker.v Util.vo
	$(call coqc,CheckerMaker.v)

Micromega.vo micromega.ml micromega.mli: Util.vo Refl.vo CheckerMaker.vo Micromega.v
	$(call coqc,Micromega.v)

micromega.cmi : micromega.mli
	ocamlc -g  -c -dtypes micromega.mli

# Extracted code
micromega.cmx: micromega.ml micromega.cmi
	$(call ocamlcomp, micromega.ml)

utils.cmx : utils.ml micromega.cmx
	$(call ocamlcomp, utils.ml)

sos.cmx : sos.ml
	$(call ocamlcomp, sos.ml)

g_micromega.cmx : g_micromega.ml4 coq_micromega.cmx
	$(call ocamlp4, g_micromega.ml4)


certificate.cmx : micromega.cmx utils.cmx fourier_num.cmx sos.cmx certificate.ml
	$(call ocamlcomp, certificate.ml)


coq_micromega.cmx : coq_micromega.ml micromega.cmx utils.cmx certificate.cmx
	$(call ocamlcomp, coq_micromega.ml)

micromega.cmxa : coq_micromega.cmx g_micromega.cmx micromega.cmx utils.cmx  fourier_num.cmx sos.cmx certificate.cmx 
	@ocamlopt -a -o micromega.cmxa   utils.cmx fourier_num.cmx micromega.cmx sos.cmx certificate.cmx     coq_micromega.cmx  g_micromega.cmx  
	@echo ocamllib -a -o micromega   utils micromega  fourier_num coq_micromega  g_micromega  

fourier_num.cmx  : fourier_num.ml
	$(call ocamlcomp, fourier_num.ml)



micromega.opt : micromega.cmxa
	$(call mktop,-opt -o micromega.opt  nums.cmxa micromega.cmxa)


preMicromegatac.vo : preMicromegatac.v micromega.opt
	./micromega.opt -compile preMicromegatac

Zpol.vo : Zpol.v 
	./micromega.opt -compile Zpol

Micromegatac.vo : preMicromegatac.vo Zpol.vo Micromegatac.v micromega.opt
	./micromega.opt -compile Micromegatac



##END
