#include <stdlib.h>
#include <stdio.h>

signed long a;
signed long n;
signed long foo;
signed long bar;
signed long baz;

signed long count(signed long a, signed long n, signed long x) {
  signed long c;
  signed long i;
  c = (0);
  i = (0);
  while ((i) < (n)) {
    if ((((signed long*)a)[i]) == (x)) {
      c = ((c) + (1));
    }
    i = ((i) + (1));
  }
  return(c);
}

signed long main() {
  a = (malloc (sizeof(signed long) * (10)));
  (((signed long*)a)[0]) = (44);
  (((signed long*)a)[1]) = (98);
  (((signed long*)a)[2]) = (44);
  (((signed long*)a)[3]) = (44);
  (((signed long*)a)[4]) = (54);
  (((signed long*)a)[5]) = (1);
  (((signed long*)a)[6]) = (92);
  (((signed long*)a)[7]) = (84);
  (((signed long*)a)[8]) = (44);
  (((signed long*)a)[9]) = (44);
  n = (10);
  (foo) = (count(a, n, 5));
  (bar) = (count(a, n, 84));
  (baz) = (count(a, n, 44));
}
