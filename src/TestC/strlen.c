#include <stdlib.h>
#include <stdio.h>

signed long a;
signed long l;

signed long create_array(signed long n) {
  signed long p;
  signed long i;
  p = (malloc (sizeof(signed long) * ((n) + (1))));
  i = (0);
  while ((i) < (n)) {
    (((signed long*)p)[i]) = ((i) + (1));
    i = ((i) + (1));
  }
  (((signed long*)p)[i]) = (0);
  return(p);
}

signed long str_len(signed long a) {
  signed long p;
  signed long l;
  p = (a);
  l = (0);
  while (*((signed long*)p)) {
    l = ((l) + (1));
    p = ((p) + (8));
  }
  return(l);
}

signed long main() {
  (a) = (create_array(5));
  (l) = (str_len(a));

//Code manually added by me to check results
 printf("%ld,%ld,%ld,%ld,%ld,%ld\n",
   (((signed long*)a)[0]),
   (((signed long*)a)[1]),
   (((signed long*)a)[2]),
   (((signed long*)a)[3]),
   (((signed long*)a)[4]),
   (((signed long*)a)[5])
 );

  printf("the length of the array is: %ld.\n", l);
}
