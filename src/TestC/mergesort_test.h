#include "minunit.h"

int tests_run = 0;
signed long n1;
signed long * a1;

static char * test_length_array() {
  mu_assert("error, n != 10", n1 == 10);
  return 0;
 }

static char * test_sorted_array() {
  int i=0;
  int sorted = 1;
  while (i < n1 - 1) {
    if (a1[i] > a1[i+1]) {
      printf("%ld > %ld\n", a1[i], a1[i+1]);
      sorted = 0;
    }
    ++i;
  };
  mu_assert("error, array is not sorted", sorted == 1);
  return 0;
 }

static char * all_tests() {
  mu_run_test(test_length_array);
  mu_run_test(test_sorted_array);
  return 0;
}

signed long test_main(signed long a, signed long n, signed long (*mergesort) (signed long, signed long)) {
  n1 = n;
  a1 = a;
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
