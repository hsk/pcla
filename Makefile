all:
	swipl main.pl lib/hol.cl > hol.txt
	diff lib/hol.txt hol.txt
	rm hol.txt

