#include "minunit.h"

int tests_run = 0;
signed long n1;
signed long * a1;
signed long * a2;

static char * test_length_array() {
  mu_assert("error, n != 10", n1 == 10);
  return 0;
 }

static char * test_sorted_array_program() {
  int i=0;
  int sorted = 1;
  while (i < n1 - 1) {
    if (a1[i] > a1[i+1]) {
      sorted = 0;
    }
    ++i;
  };
  mu_assert("error, array is not sorted", sorted == 1);
  return 0;
 }

static char * test_sorted_array_all_neg() {
  int i=0;
  int sorted = 1;
  while (i < n1 - 1) {
    if (a2[i] > a2[i+1]) {
      printf("%ld > %ld\n", a2[i], a2[i+1]);
      sorted = 0;
    }
    ++i;
  };
  mu_assert("error, array is not sorted", sorted == 1);
  return 0;
 }

static char * all_tests() {
  mu_run_test(test_length_array);
  mu_run_test(test_sorted_array_program);
  mu_run_test(test_sorted_array_all_neg);
  return 0;
}

signed long test_main(signed long a, signed long n, signed long (*bubblesort) (signed long, signed long)) {
  a1 = a;
  n1 = n;

  a2 = (malloc (sizeof(signed long) * (10)));
  ((a2)[0]) = (-44);
  ((a2)[1]) = (-1);
  ((a2)[2]) = (-60);
  ((a2)[3]) = (-26);
  ((a2)[4]) = (-54);
  ((a2)[5]) = (-1);
  ((a2)[6]) = (-92);
  ((a2)[7]) = (-84);
  ((a2)[8]) = (-38);
  ((a2)[9]) = (-80);

  bubblesort(a2,n);

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
