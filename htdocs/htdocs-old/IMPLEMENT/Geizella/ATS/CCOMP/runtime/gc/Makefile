#CCFLAG=-g
CCFLAG=-O3

gc.o: gc.c gc.h
	gcc $(CCFLAG) -o gc.o -c gc.c

gc_mt.o: gc.c gc.h
	gcc $(CCFLAG) -DATS_MULTITHREAD -pthread -o gc_mt.o -c gc.c

clean::
	rm -f *~
