ALLOYPATH=../alloy4.2 
SOLVER_COMMAND=~/glucose-syrup-4.1/simp/glucose_static
TIMEOUT=3600
ALS=$(wildcard *.als)
RESULTS=$(patsubst %.als,%.txt,$(ALS))

default: all

all: $(RESULTS)


%.txt: %.als
	../check_aarch64_litmus.sh $< $(TIMEOUT) $(ALLOYPATH) $(SOLVER_COMMAND)


clean:
	rm *.txt
