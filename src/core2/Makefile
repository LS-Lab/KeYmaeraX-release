E ?= TCore.scala

.PHONY : doc

run: $E
	@echo "================================="
	scala -deprecation $E

# Clean #######

clean:
	rm -f *.scala~ *.class *.pvs~ *.tex~ Makefile~
	rm -rf pvsbin