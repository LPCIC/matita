all: matita/matita/matita

.PHONY: matita/matita/matita

matita/matita/matita: elpi/elpi.cmxa matita/Makefile.defs
	$(MAKE) -C matita

matita/Makefile.defs:
	cd matita && autoconf && ./configure

elpi/elpi.cmxa:
	git submodule update --init
	$(MAKE) -C elpi

clean:
	$(MAKE) -C elpi clean
	$(MAKE) -C matita clean

run: matita/matita/matita
	TJPATH=`pwd`/elpi ./matita/matita/matita -elpi FG1 matita/matita/lib/arithmetics/nat.ma

print:
	cd refiner-CSC;\
	../elpi/elpi ../elpi/utils/elpi2mathjx.elpi -exec \
		main -- PTS_refiner_engine.elpi ../refiner-CSC.html \
		pervasives test_refiner test_kernel list logic
