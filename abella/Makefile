all: lib.thc copy.thc

lib.thc: lib.thm
	./abella lib.thm -c lib.thc -o lib.out

copy.thc: copy.thm
	./abella copy.thm -c copy.thc -o copy.out
