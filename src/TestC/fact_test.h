#include "minunit.h"

int tests_run = 0;
signed long n1;
signed long r0;
signed long r1;
signed long r2;
signed long r3;
signed long r4;
signed long r5;
signed long r6;
signed long r7;
signed long r8;
signed long r9;
signed long r10;

static char * test_fact0() {
  mu_assert("error, fact(0) != 1", r0 == 1);
  return 0;
 }

static char * test_fact1() {
  mu_assert("error, fact(1) != 1", r1 == 1);
  return 0;
 }

static char * test_fact2() {
  mu_assert("error, fact(2) != 2", r2 == 2);
  return 0;
 }

static char * test_fact3() {
  mu_assert("error, fact(3) != 6", r3 == 6);
  return 0;
 }

static char * test_fact4() {
  mu_assert("error, fact(4) != 24", r4 == 24);
  return 0;
 }

static char * test_fact5() {
  mu_assert("error, fact(5) != 120", r5 == 120);
  return 0;
 }

static char * test_fact6() {
  mu_assert("error, fact(6) != 720", r6 == 720);
  return 0;
 }

static char * test_fact7() {
  mu_assert("error, fact(7) != 5040", r7 == 5040);
  return 0;
 }

static char * test_fact8() {
  mu_assert("error, fact(8) != 40320", r8 == 40320);
  return 0;
 }

static char * test_fact9() {
  mu_assert("error, fact(9) != 362880", r9 == 362880);
  return 0;
 }

static char * test_fact10() {
  mu_assert("error, fact(10) != 3628800", r10 == 3628800);
  return 0;
 }

static char * all_tests() {
  mu_run_test(test_fact0);
  mu_run_test(test_fact1);
  mu_run_test(test_fact2);
  mu_run_test(test_fact3);
  mu_run_test(test_fact4);
  mu_run_test(test_fact5);
  mu_run_test(test_fact6);
  mu_run_test(test_fact7);
  mu_run_test(test_fact8);
  mu_run_test(test_fact9);
  mu_run_test(test_fact10);
  return 0;
}

signed long test_main(signed long n, signed long r, signed long (*fact) (signed long)) {
  n1 = n;
  r5 = r;
  r0 = fact(0);
  r1 = fact(1);
  r2 = fact(2);
  r3 = fact(3);
  r4 = fact(4);
  r6 = fact(6);
  r7 = fact(7);
  r8 = fact(8);
  r9 = fact(9);
  r10 = fact(10);

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
