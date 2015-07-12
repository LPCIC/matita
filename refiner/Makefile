TJ="../teyjus/source/"

run: refiner.lp delay.lp
	rlwrap $(TJ)tjsim refiner

refiner.lp: refiner.sig refiner.mod
	$(TJ)tjcc refiner
	$(TJ)tjlink refiner

delay.lp: delay.sig delay.mod
	$(TJ)tjcc delay
	$(TJ)tjlink delay

