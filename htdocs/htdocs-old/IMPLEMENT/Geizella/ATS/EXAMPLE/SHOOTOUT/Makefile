all: binary-trees binary-trees-lin \
     fannkuch fasta k-nucleotide mandelbrot nbody nsieve nsieve-bits \
     partial-sums pidigits recursive reverse-complement spectral-norm \
     sum-file

binary-trees: binary-trees.dats
	atscc -O3 binary-trees.dats -o binary-trees -D__ATS_gcats
binary-trees-lin: binary-trees-lin.dats
	atscc -O3 binary-trees-lin.dats -o binary-trees-lin -D__ATS_gcats
fannkuch: fannkuch.dats
	atscc -O3 -fomit-frame-pointer fannkuch.dats -o fannkuch
fasta: fasta.dats
	atscc -O3 fasta.dats -o fasta
k-nucleotide: k-nucleotide.dats symtbl.dats symtbl.sats
	atscc -O3 k-nucleotide.dats symtbl.dats symtbl.sats -o k-nucleotide -D__ATS_gcats
mandelbrot: mandelbrot.dats
	atscc -O3 mandelbrot.dats -o mandelbrot
nbody: nbody.dats
	atscc -O3 nbody.dats -o nbody -lm
nsieve: nsieve.dats
	atscc -O3 nsieve.dats -o nsieve
nsieve-mt: nsieve-mt.dats
	atscc -O3 nsieve-mt.dats -o nsieve-mt -lm
nsieve-bits: nsieve-bits.dats
	atscc -g nsieve-bits.dats -o nsieve-bits
partial-sums: partial-sums.dats
	atscc -O3 partial-sums.dats -o partial-sums -lm
pidigits: pidigits.dats
	atscc -O3 pidigits.dats -o pidigits -lgmp
recursive: recursive.dats
	atscc -O3 -fomit-frame-pointer recursive.dats -o recursive
reverse-complement: reverse-complement.dats
	atscc -O3 reverse-complement.dats -o reverse-complement
spectral-norm: spectral-norm.dats
	atscc -O3 spectral-norm.dats -o spectral-norm -lm
sum-file: sum-file.dats
	atscc -O3 sum-file.dats -o sum-file

# cleanup

clean::
	if [ -f binary-trees ] ; then rm binary-trees ; fi
	if [ -f binary-trees-lin ] ; then rm binary-trees-lin ; fi
	if [ -f fannkuch ] ; then rm fannkuch ; fi
	if [ -f fasta ] ; then rm fasta ; fi
	if [ -f k-nucleotide ] ; then rm k-nucleotide ; fi
	if [ -f mandelbrot ] ; then rm mandelbrot ; fi
	if [ -f nbody ] ; then rm nbody ; fi
	if [ -f nsieve ] ; then rm nsieve ; fi
	if [ -f nsieve-bits ] ; then rm nsieve-bits ; fi
	if [ -f partial-sums ] ; then rm partial-sums ; fi
	if [ -f pidigits ] ; then rm pidigits ; fi
	if [ -f recursive ] ; then rm recursive ; fi
	if [ -f reverse-complement ] ; then rm reverse-complement ; fi
	if [ -f spectral-norm ] ; then rm spectral-norm ; fi
	if [ -f sum-file ] ; then rm sum-file ; fi
	rm -f *_dats.c *_sats.c *~
