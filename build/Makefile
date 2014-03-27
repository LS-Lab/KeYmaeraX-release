
SRC ?= TermTests KeymaeraParser KeymaeraSymbols KeymaeraPrettyPrinter Expressions Proof Tactics Scheduler Tool SchedulerTests

SOURCES = $(addprefix ../src/edu/cmu/cs/ls/keymaera/**/, $(addsuffix .scala, $(SRC)))

all:
	scalac -deprecation -feature $(SOURCES)

