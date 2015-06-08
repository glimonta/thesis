#include "minunit.h"

int tests_run = 0;
signed long n1;
signed long * a1;
signed long foo1;
signed long bar1;
signed long baz1;

static char * test_foo_occurrences() {
  mu_assert("error, occurs(5) != 0", foo1 == 0);
  return 0;
 }

static char * test_bar_occurrences() {
  mu_assert("error, occurs(84) != 1", bar1 == 1);
  return 0;
 }

static char * test_baz_occurrences() {
  mu_assert("error, occurs(44) != 5", baz1 == 5);
  return 0;
 }

static char * all_tests() {
  mu_run_test(test_foo_occurrences);
  mu_run_test(test_bar_occurrences);
  mu_run_test(test_baz_occurrences);
  return 0;
}

signed long test_main(
  signed long n,
  signed long a,
  signed long foo,
  signed long bar,
  signed long baz)
{
  n1 = n;
  a1 = a;
  foo1 = foo;
  bar1 = bar;
  baz1 = baz;
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
