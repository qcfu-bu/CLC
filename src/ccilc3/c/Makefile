CC=gcc
RMF=rm -rf
CFLAGS=-g -O2
SRC = main.c runtime.c chan.c queue.c

all: main.out

main.out: $(SRC) 
	$(CC) $(CFLAGS) $^ -o $@

clean:: ; $(RMF) *.dSYM
clean:: ; $(RMF) *.gch
clean:: ; $(RMF) *.out