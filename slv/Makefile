SAN = -fsanitize=address -fsanitize=undefined
CFLAGS = $(SAN) -g -Wall -O2 -std=c99
LDFLAGS = $(SAN)
CC = clang

all: dpll

clean:
	rm -f *.o dpll

dpll: util.o dimacs.o dpll.o
	$(CC) $(LDFLAGS) $^ -o $@

%.o: %.c all.h
	$(CC) $(CFLAGS) -c $<

.PHONE: all clean
