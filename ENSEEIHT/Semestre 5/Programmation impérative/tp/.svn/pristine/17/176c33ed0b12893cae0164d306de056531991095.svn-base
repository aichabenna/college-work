#include <stdlib.h> 
#include <stdio.h>
#include <assert.h>
#include <math.h>

// Definition du type Point 
struct Point {
    int X, Y;
};
typedef struct Point Point;

int main(){
    // Déclarer deux variables ptA et ptB de types Point
    Point ptA, ptB;
    // Initialiser ptA à (0,0)
    ptA.X = 0;
    ptA.Y=0;
    // Initialiser ptB à (10,10)
    ptB.X = 10;
    ptB.Y=10;
    // Calculer la distance entre ptA et ptB.
    float distance = (ptA.X - ptB.X)*(ptA.X - ptB.X) + (ptA.Y - ptB.Y)*(ptA.Y - ptB.Y);
    distance = sqrt( (float) distance);
    printf("distance = %f\n", distance);
    assert( (int)(distance*distance) == 200);
    int d= (int)distance*distance;
    printf("distance*distance = %d\n",d);    
    return EXIT_SUCCESS;
}
