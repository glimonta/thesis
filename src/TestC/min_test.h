#include "minunit.h"

int tests_run = 0;
signed long n1;
signed long * a1;
signed long m1;

static char * test_min() {
  mu_assert("error, m != 1", m1 == 1);
  return 0;
 }


static char * all_tests() {
  mu_run_test(test_min);
  return 0;
}

signed long test_main(
  signed long a,
  signed long n,
  signed long m,
  signed long (*min) (signed long, signed long))
{
  n1 = n;
  a1 = a;
  m1 = m;
  char *result = all_tests();
  if (result != 0) {
      printf("%s\n", result);
  }
  else {
      printf("ALL TESTS PASSED\n");
  }
  printf("Tests run: %d\n", tests_run);

  return result != 0;
}
