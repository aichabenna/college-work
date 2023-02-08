#include <stdlib.h> 
#include <stdio.h>
#include <assert.h>
#include <stdbool.h>

#define NOMBRE 5

// Definition du type monnaie
struct monnaie{
    float valeur; 
    char devise;
};
typedef struct monnaie monnaie;
/**
 * \brief Initialiser une monnaie 
 * \param monnaie in out : pointeur vers une structure de type monnaie
 * \param valeur in : la valeur de la monnaie
 * \param devide in : la devise de la monnaie
 * \pre valeur >0
 * // TODO
 */ 
void initialiser(monnaie *monnaie, float valeur, char devise){
    // TODO
    assert(valeur >0.0);
    monnaie->valeur=valeur;
    monnaie->devise=devise;
}


/**
 * \brief Ajouter une monnaie m2 à une monnaie m1 
 * \param m1 in : pointeur vers une monnaie
 * \param m2 in out : pointeur vers une monnaie  
 */ 
bool ajouter(monnaie *m1, monnaie *m2){
    // TODO
    if(m1->devise == m2->devise){
        m2->valeur=m2->valeur+m1->valeur;
    }
    return m1->devise == m2->devise;
}


/**
 * \brief Tester Initialiser 
 * \param[]
 * 
 */ 
void tester_initialiser(){
    monnaie m;
    initialiser(&m,15.0, 'e');
    assert( m.valeur==15.0 && m.devise=='e');
}

/**
 * \brief Tester Ajouter 
 * \param[]
 * 
 */ 
void tester_ajouter(){
    // TODO
    monnaie m1;
    monnaie m2;
    // test avec deux devises différentes
    initialiser(&m1,15.5, 'e');
    initialiser(&m2,20.0, '$');
    assert (!(ajouter(&m1,&m2)));
    // test avec deux devises identiques
    initialiser(&m2,20.0, 'e');
    assert( ajouter(&m1,&m2) && m2.valeur==35.5 && m1.valeur==15.5);
}



int main(void){
    //Tests:
    tester_initialiser();
    tester_ajouter();
    // Un tableau de 5 monnaies
    monnaie porte_monnaie[NOMBRE];
    //Initialiser les monnaies
    float valeur;
    char devise;
    printf("Début du remplissage du tableau ...\n");
    for (int i=0; i<NOMBRE;i++){
        printf("Entrez une monnaie (valeur + devise) :\n");
        scanf("%f %c", &valeur, &devise);
        fgetc(stdin);
        initialiser(&porte_monnaie[i],valeur, devise);
    }
    printf("Fin du remplissage\n");

    // Afficher la somme des toutes les monnaies qui sont dans une devise entrée par l'utilisateur.

    printf("Entrez une devise: \n");
    scanf("%c", &devise);
    monnaie m;
    bool ajoute= true;
    m.valeur = 0.0;
    m.devise = devise;
    for (int i=0; i<NOMBRE; i++){
        if (ajoute && (porte_monnaie+i)->devise == devise){
            ajoute = ajouter(&porte_monnaie[i], &m);
        }
    }
    printf("La somme de toutes les monnaies qui sont dans une devise %c est %f\n", m.devise, m.valeur );
    return EXIT_SUCCESS;
}
