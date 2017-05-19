To use Matita with embedded ELPI

*) run a matita script

in matita/matita/lib/* run "../../matita.opt" or "../../matitac.opt"
on the script, with the options below:

required:
  -elpi <kernel>  the prolog kernel to use: NO, CSC, FG0, FG1

CSC is the ufficial kernel/elaborator for DALEFEST
FG0 and FG1 are experimental kernels/elaborators

optional:
  -elpi-quiet  turn off prolog informational prints
  -elpi-cache  turn on prolog query caching
