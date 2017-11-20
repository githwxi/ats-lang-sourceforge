#ATSCCFLAG=-g
ATSCCFLAG=-O3

gc.o: gc.dats gc.sats gc.cats gc.hats \
      globals.cats block0.cats block1.cats \
      marking.cats sweeping.cats collecting.cats
	atscc $(ATSCCFLAG) -c gc.dats gc.sats
	ld -r -o gc.o gc_dats.o gc_sats.o

clean::
	rm -f gc_dats.c gc_sats.c *~
