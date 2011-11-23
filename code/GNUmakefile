IDIR =./include
CC=gcc
CFLAGS=-I$(IDIR)

ODIR=./obj
LDIR =./lib

LIBS=-lm

_DEPS = formula.h proof.h
DEPS = $(patsubst %,$(IDIR)/%,$(_DEPS))

_OBJ = formula.o proof.o 
OBJ = $(patsubst %,$(ODIR)/%,$(_OBJ))

$(ODIR)/%.o: %.c $(DEPS)
	mkdir -p $(ODIR)
	$(CC) -c -o $@ $< $(CFLAGS)

prover: $(OBJ)
	gcc -o $@ $^ $(CFLAGS) $(LIBS)

.PHONY: clean

clean:
	rm -f $(ODIR)/*.o *~ core $(INCDIR)/*~ 
	rm -rf $(ODIR)
	rm prover