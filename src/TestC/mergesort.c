#include <stdlib.h>
#include <stdio.h>
#include "mergesort_test.h"

signed long a;
signed long n;

signed long merge(signed long a, signed long n, signed long m) {
  signed long i;
  signed long j;
  signed long k;
  signed long x;
  x = (malloc (sizeof(signed long) * (n)));
  i = (0);
  j = (m);
  k = (0);
  while ((k) < (n)) {
    if ((j) == (n)) {
      (((signed long*)x)[k]) = (((signed long*)a)[i]);
      i = ((i) + (1));
    } else {
      if ((i) == (m)) {
        (((signed long*)x)[k]) = (((signed long*)a)[j]);
        j = ((j) + (1));
      } else {
        if ((((signed long*)a)[j]) < (((signed long*)a)[i])) {
          (((signed long*)x)[k]) = (((signed long*)a)[j]);
          j = ((j) + (1));
        } else {
          (((signed long*)x)[k]) = (((signed long*)a)[i]);
          i = ((i) + (1));
        }
      }
    }
    k = ((k) + (1));
  }
  i = (0);
  while ((i) < (n)) {
    (((signed long*)a)[i]) = (((signed long*)x)[i]);
    i = ((i) + (1));
  }
  free(&((*((signed long*)x))));
}

signed long mergesort(signed long a, signed long n) {
  signed long m;
  signed long x;
  if ((n) < (2)) {
    return;
  } else {
    m = ((n) / (2));
    mergesort(a, m);
    mergesort((signed long*)& (((signed long*)a)[m]), (n) + (- (m)));
  }
  merge(a, n, m);
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
  mergesort(a, n);
  test_main(n,a);
}
