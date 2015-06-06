#include <stdlib.h>
#include <stdio.h>

signed long n;
signed long r;

signed long fib(signed long n) {
  signed long r;
  signed long x;
  signed long t;
  if ((n) == (0)) {
    return(0);
  } else {
    if ((n) == (1)) {
      return(1);
    } else {
      x = (0);
      r = (1);
      n = ((n) + (-1));
      while ((0) < (n)) {
        t = ((x) + (r));
        x = (r);
        r = (t);
        n = ((n) + (-1));
      }
      return(r);
    }
  }
}

signed long main() {
  n = (14);
  (r) = (fib(n));

//Code manually added by me to check results
  printf("the fibonacci number of %ld is %ld.\n", n, r);

}
