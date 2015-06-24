H = @

TJCC     = $(HOME)/lpcic/teyjus/tjcc
TJLINK   = $(HOME)/lpcic/teyjus/tjlink
TJSIM    = $(HOME)/lpcic/teyjus/tjsim -b -m 0
TJDEPEND = $(HOME)/lpcic/teyjus/tjdepend
TIME     = `which time` -p -a

MODULES = helena grundlagen

all: $(MODULES:%=%.lp)

depend: .depend

test: grundlagen.lp
	@echo SYM -s main. $(<:%.lp=%)
	$(H)$(TIME) $(TJSIM) -s main. $(<:%.lp=%)

profile: profile.txt

clear:
	$(H)$(RM) *.lp *.lpo .depend profile.txt *~

%.lpo: %.mod %.sig
	@echo CC $*
	$(H)$(TJCC) $*

%.lp: %.lpo
	@echo LINK $*
	$(H)$(TJLINK) $*

.depend: $(MODULES:%=%.mod) $(MODULES:%=%.sig)
	@echo DEPEND $(MODULES)
	$(H)$(TJDEPEND) $(MODULES) > $@

profile.txt: TMP = tmp.txt

profile.txt: grundlagen.lp
	@echo [31 times] SYM -s main. $(<:%.lp=%)
	$(H)for RUN in `seq 31`; do $(TIME) -o $(TMP) $(TJSIM) -s main. $(<:%.lp=%); done
	$(H)grep user tmp.txt | sort > $@
	$(H)$(RM) $(TMP)

ifneq ($(MAKECMDGOALS), depend)
   include .depend   
endif

.PHONY: all depend test profile clear
