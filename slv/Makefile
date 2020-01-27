OPT = -fsanitize=address -fsanitize=undefined -O0 -g
#OPT = -DNDEBUG -O3
CFLAGS = $(OPT) -Wall -std=c99
LDFLAGS = $(OPT)

all: dpll

test: all
	@./test.sh

clean:
	rm -f *.o dpll

dpll: util.o dimacs.o dpll.o
	$(CC) $(LDFLAGS) $^ -o $@

%.o: %.c all.h
	$(CC) $(CFLAGS) -c $<

.PHONE: all test clean
