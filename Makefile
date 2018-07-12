test:
	swipl syntax_check.pl lib/hol.cl
	swipl pcla.pl lib/hol.cl > hol.txt
	diff lib/hol.txt hol.txt
	rm hol.txt
	@echo "test ok"
