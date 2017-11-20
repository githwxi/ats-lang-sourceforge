#Berkeley Yacc
YACC=byacc
GCFLAG=-D__ATS_gcats
GCFLAG=-D__ATS_gc
#GCFLAG=-D__ATS_GC
#GCFLAG=
ATSCCFLAG=-g

calc: calc_lats_dats.c calc_dats.c calc_yats.c
	atscc $(ATSCCFLAG) $(GCFLAG) -o calc calc_yats.c calc_lats_dats.c -latslex
calc_lats.dats: calc.lats; atslex < calc.lats > calc_lats.dats
calc_lats_dats.c: calc_lats.dats; atscc -cc calc_lats.dats
calc_dats.c: calc.dats; atscc -cc calc.dats
calc_yats.c: calc.yats; $(YACC) -d -o calc_yats.c calc.yats

clean::
	rm -f *.o *_lats.dats *_dats.c *_yats.c *_yats.h *~
