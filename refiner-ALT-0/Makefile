H = @

ENGINE = kernel_engine.elpi
EXPORT = export-pts

ELPI       = ../elpi/elpi
ELPI_OPTS  = -I ../lib
HELENA_DIR = helena

TEMP = etc/temp.txt
TEST = etc/test_31.txt

all:

clean:
	$(H)$(RM) -f *~

test-tc:
	$(H)$(ELPI) $(ELPI_OPTS) -test $(ENGINE)

test:
	$(H)$(ELPI) $(ELPI_OPTS) -no-tc -test $(ENGINE)

test-31:
	$(H)mkdir -p etc
	$(H)$(RM) $(TEMP)
	$(H)for RUN in `seq 1 31`; do $(ELPI) $(ELPI_OPTS) -no-tc -test $(ENGINE) 2>> $(TEMP); done
	$(H)echo `hostname` `date` > $(TEST)
	$(H)echo >> $(TEST)
	$(H)grep "Time: " $(TEMP) | sort -n -k 2 | cat -n >> $(TEST)

helena:
	$(H)$(MAKE) --no-print-directory -C $(HELENA_DIR) $(EXPORT)

.PHONY: all clean test-tc test test-31 helena
