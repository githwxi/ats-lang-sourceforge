all: \
  getword \

######

html::
	atsopt --posmark_html_only -d getword.dats

######

getword: getword.dats
	atscc -o getword getword.dats

######

clean::
	rm -f a.out *_dats.c *.o *~

cleanall: clean
	rm -f *_dats.html 
	rm -f getword

###### end of [Makefile] ######
