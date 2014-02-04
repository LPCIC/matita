TJ="$(HOME)/work-area/PROLOG/teyjus/source/"

run: refiner.lp
	rlwrap $(TJ)tjsim refiner

refiner.lp: refiner.sig refiner.mod
	$(TJ)tjcc refiner
	$(TJ)tjlink refiner

