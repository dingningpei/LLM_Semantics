CPLEX_AVAILABLE = false
LEMON_AVAILABLE = false
CC = g++
#CC = ~/gcc-4.3.0/bin/g++
CPPFLAGS = -g -std=c++0x -O3 -I .
CPPFLAGS += -Wall -Werror=return-type -Wno-non-virtual-dtor -Wno-unused-function -Wno-deprecated
CPPFLAGS += -DNDEBUG
CPPFLAGS += -pg -ggdb

ifeq ($(CPLEX_AVAILABLE),true)
ifeq ($(LEMON_AVAILABLE),true)
CPPFLAGS += -I${HOME}/WORK/cplex124/cplex/include
CPPFLAGS += -DCPLEX_AVAILABLE=1
CPPFLAGS += -DLEMON_AVAILABLE=1
CPLEX_AND_LEMON_OPT = -lcplex124 -lemon
else
CPPFLAGS += -DCPLEX_AVAILABLE=0
CPPFLAGS += -DLEMON_AVAILABLE=0
endif
endif

# Work out the architecture.
ifeq ($(shell uname -m),x86_64)
CPPFLAGS += -m64
else
ifeq ($(shell uname -s),Darwin)
CPPFLAGS += -m64
else
CPPFLAGS += -m32
endif
endif

ifeq ($(PARALLEL),true)
#CC = /usr/lib64/lam/bin/mpic++
#CC = /usr/lib64/openmpi/1.4-gcc/bin/mpic++
CC = /usr/bin/mpic++
CPPFLAGS += -DPARALLEL
endif

SRCS = $(wildcard core/*.c) $(wildcard vars/*.c) $(wildcard branching/*.c) $(wildcard primitives/*.c) $(wildcard globals/*.c) $(wildcard parallel/*.c) $(wildcard mip/*.c) $(wildcard ldsb/*.c) $(wildcard mdd/*.c) $(wildcard mymip/*.c) $(wildcard support/*.c) $(wildcard LiMDD/*.c) $(wildcard circuit/*.cpp)

OBJS = $(addsuffix .o, $(basename $(SRCS)))
DEPS = $(addsuffix .d, $(basename $(SRCS)))

FLATZINCSRC = $(wildcard flatzinc/*.c)
FLATZINCOBJ = $(addsuffix .o, $(basename $(FLATZINCSRC)))
FLATZINCDEP = $(addsuffix .d, $(basename $(FLATZINCSRC)))

EXAMPLESRC =  $(wildcard examples/*.c)
EXAMPLEOBJ = $(addsuffix .o, $(basename $(EXAMPLESRC)))
EXAMPLEDEP = $(addsuffix .d, $(basename $(EXAMPLESRC)))
EXAMPLES = $(basename $(EXAMPLESRC))

all : fzn_chuffed
#$(EXAMPLES)

fzn_chuffed : $(FLATZINCOBJ) $(OBJS)
	$(CC) $(CPPFLAGS) -o fzn_chuffed $(FLATZINCOBJ) $(OBJS)  -L${HOME}/WORK/cplex124/cplex/bin/x86-64_sles10_4.1 $(CPLEX_AND_LEMON_OPT) -lrt 

$(EXAMPLES) : % : %.o $(OBJS)
	$(CC) $(CPPFLAGS) -o $@ $@.o $(OBJS) -L${HOME}/WORK/cplex124/cplex/bin/x86-64_sles10_4.1 $(CPLEX_AND_LEMON_OPT) -lrt 

clean :
	rm -f fzn_chuffed $(EXAMPLES) $(OBJS) $(FLATZINCOBJ) $(EXAMPLEOBJ) $(DEPS) $(FLATZINCDEP) $(EXAMPLEDEP)

-include $(DEPS)
-include $(FLATZINCDEP)
-include $(EXAMPLEDEP)

%.d: %.c
	@$(CC) -MM -MT  $(subst .d,.o,$@) -MT $@ $(CPPFLAGS) $< > $@

%.tab.h: %.tab.c
%.tab.c: %.yxx
	bison -t -o $@ -d $<

%.yy.c: %.lxx
	flex -o $@ $<
