H   = @
TMP = tmp.txt

TJCC     = ../../../../teyjus/tjcc
TJLINK   = ../../../../teyjus/tjlink
TJSIM    = ../../../../teyjus/tjsim -b
TJDEPEND = ../../../../teyjus/tjdepend
TIME     = `which time` -p -a -f "%U" -o $(TMP)
ADD      = ./add.opt -a 3

MODULES = helena grundlagen grundlagen2 grundlagen3

all: $(MODULES:%=%.lp)

depend: .depend

test: grundlagen3.lp Makefile
	@echo SYM -s main. $(<:%.lp=%)
	$(H)$(TIME) $(TJSIM) -s main. $(<:%.lp=%)

profile: profile.txt Makefile

clear:
	$(H)$(RM) *.lp *.lpo .depend profile.txt *~

%.lpo: %.mod %.sig Makefile
	@echo CC $*
	$(H)$(TJCC) $*

%.lp: %.lpo Makefile
	@echo LINK $*
	$(H)$(TJLINK) $*

.depend: $(MODULES:%=%.mod) $(MODULES:%=%.sig) Makefile
	@echo DEPEND $(MODULES)
	$(H)$(TJDEPEND) $(MODULES) > $@

profile.txt: grundlagen3.lp Makefile
	@echo [31 times] SYM -s main. $(<:%.lp=%)
	$(H)for RUN in `seq 31`; do $(TIME) $(TJSIM) -s main. $(<:%.lp=%); done
	$(H)sort $(TMP) | uniq > $@
	$(H)$(RM) $(TMP)

pippo: LINE = $(TIME) $(TJCC) helena; $(TIME) $(TJCC) grundlagen3; $(TIME) $(TJLINK) grundlagen3

pippo:
	$(H)$(RM) $(TMP)
	$(H)$(H)for RUN in `seq 31`; do $(LINE); done;
	$(H)$(ADD) < $(TMP) | sort | uniq > profile.txt
	$(H)$(RM) $(TMP)

ifneq ($(MAKECMDGOALS), depend)
   include .depend   
endif

.PHONY: all depend test profile clear
