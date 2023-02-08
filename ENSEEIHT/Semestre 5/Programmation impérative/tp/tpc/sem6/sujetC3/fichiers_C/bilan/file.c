/**
 *  \author Xavier Cr�gut <nom@n7.fr>
 *  \file file.c
 *
 *  Objectif :
 *	Implantation des op�rations de la file
*/

#include <malloc.h>
#include <assert.h>

#include "file.h"


void initialiser(File *f)
{
    // TODO
    f->tete = NULL;
    f->queue = NULL;
    assert(est_vide(*f));
}


void detruire(File *f)
{
    // TODO
    char v;
    while(!est_vide(*f)){
        extraire(f,&v);
    }
}


char tete(File f)
{
    assert(! est_vide(f));
    // TODO
    return f.tete->valeur;
}


bool est_vide(File f)
{
    // TODO
    return f.tete == NULL && f.queue == NULL;
}

/**
 * Obtenir une nouvelle cellule allou�e dynamiquement
 * initialis�e avec la valeur et la cellule suivante pr�cis� en param�tre.
 */
static Cellule * cellule(char valeur, Cellule *suivante)
{
    // TODO
    Cellule * new_cell = malloc(sizeof(Cellule));
    new_cell->valeur = valeur;
    new_cell->suivante = suivante;
    return new_cell;
}


void inserer(File *f, char v)
{
    assert(f != NULL);

    // TODO
    if(f->tete == NULL){
        f->tete = cellule(v, NULL);
        f->queue = f->tete;
    }else{
        f->queue->suivante = cellule(v, NULL);
        f->queue = f->queue->suivante;
    }
}

void extraire(File *f, char *v)
{
    assert(f != NULL);
    assert(! est_vide(*f));

    // TODO
    *v = f->tete->valeur;
    Cellule *to_be_deleted = f->tete;
    f->tete = f->tete->suivante;
    if(f->tete == NULL){
        f->queue = f->tete;
    }
    free(to_be_deleted);
    to_be_deleted = NULL;
}


int longueur(File f)
{
    // TODO
    int length=0;
    Cellule *curseur = f.tete;
    while(curseur !=NULL){
        length++;
        curseur=curseur->suivante;
    }
    return length;
}
