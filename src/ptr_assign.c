#include <stdlib.h>
#include <stdio.h>

int *p;


int *fp () {
  printf("Getting value of p\n");
  return p;
}

int f() {
    printf("Calling function f\n");
    p++;
    return 1;
}

int main () {
    p = malloc (10*sizeof(int));
    int *q=p;
    *p = 0;
    *(p + 1) = 0;
    
    *p = f();
  
    printf("%d,%d\n",q[0],q[1]);
  
}
