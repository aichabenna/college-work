#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include "treetrav.h"
#include "omp.h"

extern int countnodes[MAXTHREADS];

/* This is simply a wrapper for the recursive tree traversal
   routine */

/* This nth argument defines the number of threads to be used in the
   recursive tree traversal. */

void treetraverse_par(TreeNode *root, int nth)
{

  int depth, i;

  /* CC: just a simple rule to compute the depth. In this case we try
     to have a total number of tasks which is bigger than four times
     the number of threads*/
  depth = root->l - round(log(4 * nth) / log(2));
  if (nth == 1)
    depth = root->l;

  /* Initialize the counter to 0. MAXTHREADS is the maximum number of
     allowed threads. */
  for (i = 0; i < MAXTHREADS; i++)
    countnodes[i] = 0;

    /* CC: parallel region created with nth threads */
#pragma omp parallel num_threads(nth)
  {
    /* CC: only the master thread make the call to the recursive
       routine otherwise we will have multiple tree traversals. This
       can be done also with the omp single directive. */
#pragma omp master
    {
      /* Start the tree traversal by calling the recursive routine */
      treetraverserec_par(root, depth);
    }
  }
  return;
}

/* This recursive routine performs a topological order tree traversal
   starting from the root node pointed by *root */

/* In the second part of the excercise, the depth argument will be
   used to define a layer in the tree below which tasks will be
   undeferred and immediately executed; this allows to reduce the
   overhead of creating and handling submitted tasks. */

void treetraverserec_par(TreeNode *root, int depth)
{

  double sum;
  int i, iam, it;

  if (root->l != 1)
  {
    /* If this node is not a leaf...*/

    /* CC: the "if" condition is for stopping the creation of tasks: a
       task is created and deferred only if the node is in a level above
       depth "depth". Otherwise the task is undeferred and will be
       immediately executed with a lower overhead. In Part 1, a basic
       parallelization without the "if" condition has to be
       developed. The if has to be added in Part 2 only.*/

#pragma omp task if (root->l >= depth)
    {
      /* ...visit the left subtree... */
      treetraverserec_par(root->left, depth);
    }
#pragma omp task if (root->l >= depth)
    {
      /* ...visit the right subtree... */
      treetraverserec_par(root->right, depth);
    }

    /* CC: note that if no taskwait is done then the tree will not be
       traversed in topological order leading to incorrect result */
#pragma omp taskwait
    /* ...compute root->v as the sum of the v values on the left and
       right children... */
    root->v += (root->right)->v + (root->left)->v;
  }

  /* ...add root->n to root->v... */
  root->v += root->n;

  /* ...do some random work... */
  for (it = 0; it < NIT; it++)
    for (i = 1; i < DATASIZE; i++)
      root->data[0] += root->data[i];

  /* ...increment the counter of the number of nodes treated by the
     executing thread. */
  iam = omp_get_thread_num();
  countnodes[iam] += 1;

  return;
}
