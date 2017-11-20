######
#
# A variety of examples involving dependent and/or linear types
#
######

all: AutoDiff fft \
     hamming_lazy GaussElim \
     kmp queens pi_lazy \
     sieve sieve_lazy strmat \
     tetrix wc

# automatic differentiation
AutoDiff: AutoDiff.dats; atscc -o AutoDiff AutoDiff.dats -lm

# BlackScholes formula
BlackScholes: BlackScholes.dats; atscc -tc BlackScholes.dats

# test for Mersenne primes
fft: fft.dats; atscc -O3 -o fft fft.dats -lm

# hamming in lazy style
hamming_lazy: hamming_lazy.dats
	atscc -o hamming_lazy hamming_lazy.dats

# gassian elimination
GaussElim: GaussElim.dats; atscc -o GaussElim GaussElim.dats

# Knuth-Morris-Pratt string search
kmp: kmp.dats; atscc -o kmp kmp.dats

# the n-queen problem
queens: queens.dats; atscc -o queens queens.dats

# Euler's transform in lazy style
pi_lazy: pi_lazy.dats; atscc -o pi_lazy pi_lazy.dats

# Erathosthene's sieve
sieve: sieve.dats; atscc -o sieve sieve.dats

# Erathosthene's sieve in lazy style
sieve_lazy: sieve_lazy.dats; atscc -O3 -o sieve_lazy sieve_lazy.dats

# Erathosthene's sieve in lazy style
sieve_lazy_vt: sieve_lazy_vt.dats
	atscc -D__ATS_gcats -O3 -o sieve_lazy_vt sieve_lazy_vt.dats

# a simple implementation of string match in CPS-style
strmat: strmat.dats; atscc -o strmat strmat.dats

# a poor man's game of tetrix
tetrix: tetrix.dats; atscc -O3 -o tetrix tetrix.dats

# a simple implementation of world count
wc: wc.dats; atscc -O3 -o wc wc.dats

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/MISC

update::
	cp Makefile $(DIR)
	cp AutoDiff.dats $(DIR)
	cp BlackScholes.dats $(DIR)
	cp fft.dats $(DIR)
	cp GaussElim.dats $(DIR)
	cp hamming_lazy.dats $(DIR)
	cp kmp.dats $(DIR)
	cp pi_lazy.dats $(DIR)
	cp queens.dats $(DIR)
	cp sieve.dats $(DIR)
	cp sieve_lazy.dats $(DIR)
	cp strmat.dats $(DIR)
	cp tetrix.dats $(DIR)
	cp wc.dats $(DIR)

######

clean::
	if [ -f AutoDiff ] ; then rm AutoDiff ; fi
	if [ -f fft ] ; then rm fft ; fi
	if [ -f GaussElim ] ; then rm GaussElim ; fi
	if [ -f hamming_lazy ] ; then rm hamming_lazy ; fi
	if [ -f kmp ] ; then rm kmp ; fi
	if [ -f pi_lazy ] ; then rm pi_lazy ; fi
	if [ -f queens ] ; then rm queens ; fi
	if [ -f sieve ] ; then rm sieve ; fi
	if [ -f strmat ] ; then rm strmat ; fi
	if [ -f sieve_lazy ] ; then rm sieve_lazy ; fi
	if [ -f tetrix ] ; then rm tetrix ; fi
	if [ -f wc ] ; then rm wc ; fi
	rm -f *_dats.c *_sats.c *~
