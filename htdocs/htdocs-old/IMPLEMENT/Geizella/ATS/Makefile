###################################################################
#                                                                 #
#                        Applied Type System                      #
#                                                                 #
#                          (c) Hongwei Xi                         #
#                                                                 #
#                            2002 - 2007                          #
#                                                                 #
#                         Boston University                       #
#                                                                 #
#                   Distributed by permission only.               #
#                                                                 #
###################################################################

# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex

INCLUDES=
OCAMLFLAGS=$(INCLUDES) nums.cma unix.cma
OCAMLOPTFLAGS=$(INCLUDES) nums.cmxa unix.cmxa

SOURCES := \
  ats_misc.ml \
  ats_keywords.ml \
  ats_symbol.ml \
  ats_counter.ml \
  ats_label.ml \
  ats_symenv.ml \
  ats_filename.ml \
  ats_location.ml \
  ats_error.ml \
  ats_fixity.ml \
  ats_syntax.ml \
  ats_effect.ml \
  ats_grammar.mly \
  ats_lexer.mll \
  ats_printf_c.mll \
  ats_printf_ats.mll \
  ats_parser.ml \
  ats_string_parser.ml \
  ats_staexp1.ml \
  ats_env1.ml \
  ats_dynexp1.ml \
  ats_errmsg1.ml \
  ats_trans1.ml \
  ats_staexp2.ml \
  ats_staenv2.ml \
  ats_stacst2.ml \
  ats_svar_stamp.ml \
  ats_svar_bind.ml \
  ats_staexp2_util.ml \
  ats_dynexp2.ml \
  ats_dynexp2_util.ml \
  ats_stadynenv2.ml \
  ats_name_space.ml \
  ats_dyncst2.ml \
  ats_errmsg2.ml \
  ats_trans2.ml \
  ats_macro.ml \
  ats_metric.ml \
  ats_patcst2.ml \
  ats_dynexp3.ml \
  ats_errmsg3.ml \
  ats_staenv3.ml \
  ats_solver_fm.ml \
  ats_constraint.ml \
  ats_staexp2_solve.ml \
  ats_dynenv3.ml \
  ats_trans3_pat.ml \
  ats_trans3.ml \
  ats_hiexp.ml \
  ats_hiexp_util.ml \
  ats_trans4.ml \
  ats_ccomp.ml \
  ats_ccomp_util.ml \
  ats_ccomp_trans.ml \
  ats_ccomp_print.ml \
  ats_ccomp_main.ml \
  ats_arg.ml \
  ats_main_cc.ml \

######

MLS := $(filter %.ml, $(SOURCES))
MLYS := $(filter %.mly, $(SOURCES))
MLLS := $(filter %.mll, $(SOURCES))

SRCS := $(patsubst %.mll, %.ml, $(patsubst %.mly, %.ml, $(SOURCES)))
OBJS := $(SRCS:.ml=.cmo)
OPTOBJS := $(OBJS:.cmo=.cmx)

######

all: bin/atsopt bin/atscc bin/atslib libcats clean
	echo "ATS/Geizella is now built successfully."

bin/atsopt: $(OPTOBJS) ats_simplex.o ats_omega.o
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o bin/atsopt \
          ats_simplex.o ats_omega.o $(OPTOBJS) -cclib -lgmp

bin/atscc:
	cd utils/scripts; make atscc; mv atscc $(ATSHOME)/bin

bin/atslib:
	cd utils/scripts; make atslib; mv atslib $(ATSHOME)/bin

libcats::
	bin/atslib -all

ats_grammar.ml ats_grammar.mli: ats_syntax.ml ats_grammar.mly
	$(OCAMLYACC) -v ats_grammar.mly

ats_lexer.ml: ats_lexer.mll
	$(OCAMLLEX) ats_lexer.mll

ats_printf_c.ml: ats_printf_c.mll
	$(OCAMLLEX) ats_printf_c.mll

ats_printf_ats.ml: ats_printf_ats.mll
	$(OCAMLLEX) ats_printf_ats.mll

clean::
	rm -f *.cm[iox] *.cma *.cmxa *.o *~
	rm -f CCOMP/lib/output/*

#common rules:

.SUFFIXES: .ml .mli .cmi .cmo .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

.c.o:
	$(OCAMLOPT) -c -ccopt -std=c99 -ccopt -O3 -ccopt -funroll-loops $<

depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

include .depend
