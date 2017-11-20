##
## Makefile for [twentyfour.dats]
##

#GCFLAG=
#GCFLAG=-D__ATS_gc
GCFLAG=-D__ATS_gcats

######

twentyfour: twentyfour.dats rational.dats rational.sats
	atscc $(GCFLAG) -o twentyfour -O3 twentyfour.dats rational.dats rational.sats

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/Twentyfour

update::
	cp Makefile $(DIR)
	cp twentyfour.dats $(DIR)
	cp rational.dats $(DIR)
	cp rational.sats $(DIR)

######

clean::
	rm -f *_dats.c *_sats.c *~
