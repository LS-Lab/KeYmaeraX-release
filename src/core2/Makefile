JAVA_CP ?= -cp '.:scala-compiler.jar:scala-library.jar'
JAVA_FLAGS ?= $(JAVA_CP)

.PHONY : doc

% : %$.class
	@echo "================================="
	java $(JAVA_FLAGS) $@

%$.class : %.scala
	@echo "================================="
	scalac -deprecation $(addprefix -J, $(JAVA_FLAGS)) $<

# Clean #######

clean:
	rm -f *.scala~ *.class *.pvs~ *.tex~ Makefile~
	rm -rf pvsbin