#########################################################################
#                                                                       #
#                         Applied Type System                           #
#                                                                       #
#                              Hongwei Xi                               #
#                                                                       #
#########################################################################

#
#  ATS - Unleashing the Power of Types!
#
#  Copyright (C) 2002-2007 Hongwei Xi.
#
#  ATS is  free software;  you can redistribute it and/or modify it under
#  the  terms of the  GNU General Public License as published by the Free
#  Software Foundation; either version 2.1, or (at your option) any later
#  version.
# 
#  ATS is distributed in the hope that it will be useful, but WITHOUT ANY
#  WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
#  FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
#  for more details.
# 
#  You  should  have  received  a  copy of the GNU General Public License
#  along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
#  Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
#  02110-1301, USA.
#

#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#

######

ATSOPT=atsopt
ATSRUNTIME=$(ATSHOME)/CCOMP/runtime
ATSLIBC=$(ATSHOME)/libc

CC=gcc
INCLUDES=-I"$(ATSHOME)" -I"$(ATSRUNTIME)"

######

atscc:  atscc_main_dats.c \
          basics_sats.o basics_dats.o atscc_dats.o atscc_sats.o \
          stdio_sats.o stdlib_sats.o unistd_sats.o
	$(CC) $(INCLUDES) -O3 -o atscc atscc_main_dats.c $(ATSRUNTIME)/ats_prelude.c \
          basics_sats.o basics_dats.o atscc_sats.o atscc_dats.o \
          stdio_sats.o stdlib_sats.o unistd_sats.o

atslib: atslib_main_dats.c \
          basics_sats.o basics_dats.o atscc_sats.o atscc_dats.o atslib_dats.o atslib_sats.o \
          stdio_sats.o stdlib_sats.o unistd_sats.o
	$(CC) $(INCLUDES) -O3 -o atslib atslib_main_dats.c $(ATSRUNTIME)/ats_prelude.c \
          basics_sats.o basics_dats.o atscc_sats.o atscc_dats.o atslib_sats.o atslib_dats.o \
          stdio_sats.o stdlib_sats.o unistd_sats.o

deltabs: deltabs.dats
	atscc -o deltabs -O3 deltabs.dats -D__ATS_gcats

######

basics_sats.c: basics.sats
	$(ATSOPT) --output basics_sats.c --static basics.sats

basics_dats.c: basics.sats basics.dats
	$(ATSOPT) --output basics_dats.c --dynamic basics.dats

atscc_sats.c: atscc.sats
	$(ATSOPT) --output atscc_sats.c --static atscc.sats

atscc_dats.c: basics.sats atscc.sats atscc.dats
	$(ATSOPT) --output atscc_dats.c --dynamic atscc.dats

atscc_main_dats.c: atscc_main.dats
	$(ATSOPT) --output atscc_main_dats.c --dynamic atscc_main.dats

atslib_sats.c: atslib.sats
	$(ATSOPT) --output atslib_sats.c --static atslib.sats

atslib_dats.c: basics.sats atslib.sats atslib.dats
	$(ATSOPT) --output atslib_dats.c --dynamic atslib.dats

atslib_main_dats.c: atslib_main.dats
	$(ATSOPT) --output atslib_main_dats.c --dynamic atslib_main.dats

stdio_sats.c:
	$(ATSOPT) --output stdio_sats.c --static $(ATSLIBC)/SATS/stdio.sats
stdlib_sats.c:
	$(ATSOPT) --output stdlib_sats.c --static $(ATSLIBC)/SATS/stdlib.sats
unistd_sats.c:
	$(ATSOPT) --output unistd_sats.c --static $(ATSLIBC)/SATS/unistd.sats

######

basics_sats.o: basics_sats.c; $(CC) $(INCLUDES) -O3 -c basics_sats.c
basics_dats.o: basics_dats.c; $(CC) $(INCLUDES) -O3 -c basics_dats.c
atscc_sats.o: atscc_sats.c; $(CC) $(INCLUDES) -O3 -c atscc_sats.c
atscc_dats.o: atscc_dats.c; $(CC) $(INCLUDES) -O3 -c atscc_dats.c
atslib_sats.o: atslib_sats.c; $(CC) $(INCLUDES) -O3 -c atslib_sats.c
atslib_dats.o: atslib_dats.c; $(CC) $(INCLUDES) -O3 -c atslib_dats.c

stdio_sats.o: stdio_sats.c; $(CC) $(INCLUDES) -O3 -c stdio_sats.c
stdlib_sats.o: stdlib_sats.c; $(CC) $(INCLUDES) -O3 -c stdlib_sats.c
unistd_sats.o: unistd_sats.c; $(CC) $(INCLUDES) -O3 -c unistd_sats.c

######

clean::
	rm -f *_sats.c *_dats.c *.o *~

######
