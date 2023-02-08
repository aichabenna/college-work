all: jouer_UNO test_UNO

CC=c99
CFLAGS=-Wextra -pedantic -c
LDFLAGS=

jouer_UNO: jouer_uno.c carte.c jeu.c main.c uno.c
	$(CC) $(LDFLAGS) $^ -o $@

test_UNO: test_uno.c carte.c jeu.c main.c uno.c
	$(CC) $(LDFLAGS) $^ -o $@

clean:
	rm *.o jouer_UNO test_UNO
.PHONY: clean all
