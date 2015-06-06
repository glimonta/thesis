#include <stdlib.h>
#include <stdio.h>

signed long a;
signed long n;

signed long bubblesort(signed long a, signed long n) {
  signed long i;
  signed long j;
  signed long t;
  t = (0);
  i = (1);
  while ((i) < (n)) {
    j = (0);
    while ((j) < ((n) + (-1))) {
      if ((((signed long*)a)[(j) + (1)]) < (((signed long*)a)[j])) {
        t = (((signed long*)a)[j]);
        (((signed long*)a)[j]) = (((signed long*)a)[(j) + (1)]);
        (((signed long*)a)[(j) + (1)]) = (t);
      }
      j = ((j) + (1));
    }
    i = ((i) + (1));
  }
}

signed long main() {
  a = (malloc (sizeof(signed long) * (10)));
  (((signed long*)a)[0]) = (44);
  (((signed long*)a)[1]) = (1);
  (((signed long*)a)[2]) = (60);
  (((signed long*)a)[3]) = (-26);
  (((signed long*)a)[4]) = (54);
  (((signed long*)a)[5]) = (1);
  (((signed long*)a)[6]) = (92);
  (((signed long*)a)[7]) = (84);
  (((signed long*)a)[8]) = (38);
  (((signed long*)a)[9]) = (80);
  n = (10);
  bubblesort(a, n);
}
