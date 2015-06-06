#include <stdlib.h>
#include <stdio.h>

signed long a;
signed long n;

signed long swap(signed long x, signed long y) {
  signed long t;
  t = (*((signed long*)x));
  ((*((signed long*)x))) = (*((signed long*)y));
  ((*((signed long*)y))) = (t);
}

signed long quicksort(signed long a, signed long s, signed long d) {
  signed long l;
  signed long r;
  signed long p;
  if ((s) < (d)) {
    l = ((s) + (1));
    r = (d);
    p = (((signed long*)a)[s]);
    while ((l) < (r)) {
      if ((((signed long*)a)[l]) < ((p) + (1))) {
        l = ((l) + (1));
      } else {
        if ((p) < (((signed long*)a)[r])) {
          r = ((r) + (-1));
        } else {
          swap((signed long*)& (((signed long*)a)[l]), (signed long*)& (((signed long*)a)[r]));
        }
      }
    }
    if ((((signed long*)a)[l]) < (p)) {
      swap((signed long*)& (((signed long*)a)[l]), (signed long*)& (((signed long*)a)[s]));
      l = ((l) + (-1));
    } else {
      l = ((l) + (-1));
      swap((signed long*)& (((signed long*)a)[l]), (signed long*)& (((signed long*)a)[s]));
    }
    quicksort(a, s, l);
    quicksort(a, r, d);
  } else {
    return;
  }
}

signed long main() {
  a = (malloc (sizeof(signed long) * (10)));
  (((signed long*)a)[0]) = (4);
  (((signed long*)a)[1]) = (65);
  (((signed long*)a)[2]) = (2);
  (((signed long*)a)[3]) = (31);
  (((signed long*)a)[4]) = (0);
  (((signed long*)a)[5]) = (99);
  (((signed long*)a)[6]) = (92);
  (((signed long*)a)[7]) = (83);
  (((signed long*)a)[8]) = (782);
  (((signed long*)a)[9]) = (1);
  n = (10);
  quicksort(a, 0, (n) + (-1));

//Code manually added by me to check results
 printf("%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld\n",
   (((signed long*)a)[0]),
   (((signed long*)a)[1]),
   (((signed long*)a)[2]),
   (((signed long*)a)[3]),
   (((signed long*)a)[4]),
   (((signed long*)a)[5]),
   (((signed long*)a)[6]),
   (((signed long*)a)[7]),
   (((signed long*)a)[8]),
   (((signed long*)a)[9])
 );
}
