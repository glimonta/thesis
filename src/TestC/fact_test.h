#include "minunit.h"

int tests_run = 0;
signed long n1;
signed long r1;

static char * test_factorial() {
  mu_assert("error, fact(5) != 120", r1 == 120);
  return 0;
 }

static char * all_tests() {
  mu_run_test(test_factorial);
  return 0;
}

signed long test_main(signed long n, signed long r) {
  n1 = n;
  r1 = r;
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
