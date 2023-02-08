/** Squelette du programme **/
/*********************************************************************
 *  Auteur  : Aicha Bennaghmouch
 *  Version : 
 *  Objectif : Conversion pouces/centimètres
 ********************************************************************/

#include <stdio.h>
#include <stdlib.h>

#define UN_POUCE 2.54

int main()
{
    float lg_p, lg_cm;
    float valeur;
    char unite;
    printf("Entrez une longueur (valeur + unité) : \n");
    /* Saisir la longueur */
    scanf("%f %c", &valeur, &unite);
    /* Calculer la longueur en pouces et en centimètres */
    switch (unite){
        case 'p':
        case 'P':
            lg_p = valeur;
            lg_cm = lg_p * UN_POUCE;
            break;
        case 'c':
        case 'C':
            lg_cm = valeur;
            lg_p = lg_cm / UN_POUCE;
            break;
        case 'm':
        case 'M':
            lg_cm = valeur * 100;
            lg_p = lg_cm / UN_POUCE;
            break;
        default:
            lg_p=0.;
            lg_cm=0.;
    }
    /* Afficher la longueur en pouces et en centimètres */
    printf("%f p = %f cm\n", lg_p, lg_cm);
    return EXIT_SUCCESS;
}
