
// Objectifs : Illustrer portée et masquage.

#define XXX -1

// Consigne : *** dans la suite uniquement ***, remplacer XXX par le bon résultat (une
// constante littérale).  Ne compiler et exécuter que quand tous les XXX ont été traités.

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

int main(void) {
    int x = 10;
    assert(10 == x);

    {
    int y = 7;
    assert(10 == x);
    assert(7 == y);

    {
        char x = '?';
        assert('?' == x);
        assert(7 == y);
        y = 7;
    }

    assert(10 == x);
    assert(7 == y);
    }

    assert(10 == x);

    printf("%s", "Bravo ! Tous les tests passent.\n");
    return EXIT_SUCCESS;
}
