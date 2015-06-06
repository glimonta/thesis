#include <stdlib.h>
#include <stdio.h>

signed long a;
signed long n;

signed long selectionsort(signed long a, signed long n) {
  signed long i;
  signed long m;
  signed long t;
  signed long j;
  i = (0);
  while ((i) < ((n) + (-1))) {
    m = (((signed long*)a)[i]);
    t = (i);
    j = ((i) + (1));
    while ((j) < (n)) {
      if ((((signed long*)a)[j]) < (m)) {
        m = (((signed long*)a)[j]);
        t = (j);
      }
      j = ((j) + (1));
    }
    (((signed long*)a)[t]) = (((signed long*)a)[i]);
    (((signed long*)a)[i]) = (m);
    i = ((i) + (1));
  }
}

signed long main() {
  a = (malloc (sizeof(signed long) * (10)));
  (((signed long*)a)[0]) = (44);
  (((signed long*)a)[1]) = (98);
  (((signed long*)a)[2]) = (60);
  (((signed long*)a)[3]) = (26);
  (((signed long*)a)[4]) = (54);
  (((signed long*)a)[5]) = (1);
  (((signed long*)a)[6]) = (92);
  (((signed long*)a)[7]) = (84);
  (((signed long*)a)[8]) = (38);
  (((signed long*)a)[9]) = (80);
  n = (10);
  selectionsort(a, n);
}
