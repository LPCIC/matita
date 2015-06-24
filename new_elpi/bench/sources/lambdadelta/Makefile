H = @

TJCC     = $(HOME)/lpcic/teyjus/tjcc
TJLINK   = $(HOME)/lpcic/teyjus/tjlink
TJSIM    = $(HOME)/lpcic/teyjus/tjsim -b
TJDEPEND = $(HOME)/lpcic/teyjus/tjdepend
TIME     = `which time` -p -a

MODULES = helena grundlagen

all: $(MODULES:%=%.lp)

depend: .depend

test: grundlagen.lp Makefile
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

profile.txt: TMP = tmp.txt

profile.txt: grundlagen.lp Makefile
	@echo [31 times] SYM -s main. $(<:%.lp=%)
	$(H)for RUN in `seq 31`; do $(TIME) -o $(TMP) $(TJSIM) -s main. $(<:%.lp=%); done
	$(H)grep user tmp.txt | sort > $@
	$(H)$(RM) $(TMP)

ifneq ($(MAKECMDGOALS), depend)
   include .depend   
endif

.PHONY: all depend test profile clear
