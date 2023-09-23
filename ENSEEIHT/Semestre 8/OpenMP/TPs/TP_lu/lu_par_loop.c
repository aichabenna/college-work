#include "trace.h"
#include "common.h"
#include <omp.h>


/* This routine performs the LU factorization of a square matrix by
   block-columns */

void lu_par_loop(Matrix A, info_type info){

  int i, j;

  /* Initialize the tracing system */
  trace_init();
  #pragma omp parallel private(i)
  {
  for(i=0; i<info.NB; i++){
    
    /* Do the Panel operation on column i */
    /* #pragma omp single : with this one no need to add a barrier*/
    #pragma omp single
    {
    panel(A[i], i, info);
    }
    /* Another version:
    #pragma omp master
    {
    panel(A[i], i, info);
    }
    #pragma omp barrier
    */

    /* Parallelize this loop     */
    /* At first : #pragma omp parallel for*/
    
    #pragma omp for /* no need to put {}*/
    for(j=i+1; j<info.NB; j++)
    {
      /* Update column j with respect to the result of panel(A, i) */
      update(A[i], A[j], i, j, info);
    }
  }
  }
  /* This routine applies permutations resulting from numerical
     pivoting. It has to be executed sequentially. */
  backperm(A, info);
  
  /* Write the trace in file (ignore) */
  trace_dump("trace_par_loop.svg");
  
  return;
  
}



