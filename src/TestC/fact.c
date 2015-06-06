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
  (r) = (fact(n));

//Code manually added by me to check results
  printf("the factorial of number %ld is %ld.\n", n, r);

}
