#
#
# A simple (single threaded) HTTP server implemented in ATS
#
#

server: server.dats
	atscc -o server -O3 server.dats -D__ATS_gcats

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/HttpServer

update::
	cp Makefile $(DIR)
	cp server.dats $(DIR)

######

clean::
	rm -f *_dats.c *_sats.c *~
