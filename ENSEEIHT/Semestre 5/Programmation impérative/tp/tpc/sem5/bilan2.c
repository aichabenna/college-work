#include <stdlib.h> 
#include <stdio.h>


int main(void){
    int n =10;
    int *p=NULL;
    printf("&n = %p\n", (void *) &n);
    printf("p = %p\n", (void *) p);
    {
        int a = 5;
        p = &a;
        printf("&a = %p\n", (void *) &n);
        printf("p = %p\n", (void *) &p);
        printf("*p = %d\n", *p);
    }
    printf("p = %p\n", (void *) p); 
    // p ne pointe vers rien a n'existe plus!
    printf("*p = %d\n",*p);
    {
        int n = 7;
        printf("n = %d\n", n);
        printf("&n = %p\n", (void *) &n);
    }
    printf("p = %p\n", (void *) &p);
    printf("*p = %d\n", *p);
    printf("&n = %p\n", (void *) &n);
    {
        double r = 11;
        printf("r = %f\n", r);
        printf("&r = %p\n", (void *) &r);
    }
    printf("*p = %d\n", *p);
    return EXIT_SUCCESS;
}
