#include <stdlib.h>
#include <stdio.h>

signed long n;
signed long r;

signed long fact(signed long n) {
  signed long r;
  signed long i;
  r = (1);
  i = (1);
  while ((i) < ((n) + (1))) {
    r = ((r) * (i));
    i = ((i) + (1));
  }
  return(r);
}

signed long main() {
  n = (5);
  (r) = (fact(5));

// Code not generated but written by me to check the programs
  printf("The factorial of %ld is %ld\n", n, r);
}
