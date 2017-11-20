all: fib_mt gcd_mt \
     mergesort_mt_int mergesort_mt_float \
     partial-sums_mt nsieve_mt

fib_mt: fib_mt.dats
#	atscc -o fib_mt -O3 -D__ATS_gc -DATS_MULTITHREAD -pthread fib_mt.dats
	atscc -o fib_mt -O3 -DATS_MULTITHREAD -pthread fib_mt.dats
#	atscc -o fib_mt -g -DATS_MULTITHREAD -pthread fib_mt.dats

gcd_mt: gcd_mt.dats
	atscc -o gcd_mt -O3 -DATS_MULTITHREAD -pthread gcd_mt.dats

partial-sums_mt: partial-sums_mt.dats
#	atscc -o partial-sums_mt -O3 -D__ATS_gc -DATS_MULTITHREAD -pthread partial-sums_mt.dats -lm
	atscc -o partial-sums_mt -O3 -DATS_MULTITHREAD -pthread partial-sums_mt.dats -lm

mergesort_mt_int: mergesort_mt_int.dats mergesort_mt.dats
#	atscc -o mergesort_mt_int -O3 -D__ATS_gc -DATS_MULTITHREAD -pthread mergesort_mt_int.dats -lm
	atscc -o mergesort_mt_int -O3 -DATS_MULTITHREAD -pthread mergesort_mt_int.dats -lm

mergesort_mt_float: mergesort_mt_float.dats mergesort_mt.dats
#	atscc -o mergesort_mt_float -O3 -D__ATS_gc -DATS_MULTITHREAD -pthread mergesort_mt_float.dats -lm
	atscc -o mergesort_mt_float -O3 -DATS_MULTITHREAD -pthread mergesort_mt_float.dats -lm

quicksort_mt_int: quicksort_mt_int.dats quicksort_mt.dats
#	atscc -o quicksort_mt_int -O3 -D__ATS_gc -DATS_MULTITHREAD -pthread quicksort_mt_int.dats -lm
	atscc -o quicksort_mt_int -O3 -DATS_MULTITHREAD -pthread quicksort_mt_int.dats -lm

quicksort_mt_float: quicksort_mt_float.dats quicksort_mt.dats
#	atscc -o quicksort_mt_float -O3 -D__ATS_gc -DATS_MULTITHREAD -pthread quicksort_mt_float.dats -lm
	atscc -o quicksort_mt_float -O3 -DATS_MULTITHREAD -pthread quicksort_mt_float.dats -lm

nsieve_mt: nsieve_mt.dats
#	atscc -o nsieve_mt -O3 -D__ATS_gc -DATS_MULTITHREAD -pthread nsieve_mt.dats -lm
	atscc -o nsieve_mt -O3 -DATS_MULTITHREAD -pthread nsieve_mt.dats -lm

######

clean::
	if [ -f fib ] ; then rm fib ; fi
	if [ -f fib_mt ] ; then rm fib_mt ; fi
	if [ -f gcd_mt ] ; then rm gcd_mt ; fi
	if [ -f mergesort_mt_int ] ; then rm mergesort_mt_int ; fi
	if [ -f mergesort_mt_float ] ; then rm mergesort_mt_float ; fi
	if [ -f quicksort_mt_int ] ; then rm quicksort_mt_int ; fi
	if [ -f quicksort_mt_float ] ; then rm quicksort_mt_float ; fi
	if [ -f nsieve_mt ] ; then rm nsieve_mt ; fi
	if [ -f partial-sums_mt ] ; then rm partial-sums_mt ; fi
	rm -f *_dats.c *_sats.c *~
