#include "minunit.h"

int tests_run = 0;
signed long n1;
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
signed long r11;
signed long r12;
signed long r13;
signed long r14;

static char * test_fib1() {
  mu_assert("error, fib(1) != 1", r1 == 1);
  return 0;
 }

static char * test_fib2() {
  mu_assert("error, fib(2) != 1", r2 == 1);
  return 0;
 }

static char * test_fib3() {
  mu_assert("error, fib(3) != 2", r3 == 2);
  return 0;
 }

static char * test_fib4() {
  mu_assert("error, fib(4) != 3", r4 == 3);
  return 0;
 }

static char * test_fib5() {
  mu_assert("error, fib(5) != 5", r5 == 5);
  return 0;
 }

static char * test_fib6() {
  mu_assert("error, fib(6) != 8", r6 == 8);
  return 0;
 }

static char * test_fib7() {
  mu_assert("error, fib(7) != 13", r7 == 13);
  return 0;
 }

static char * test_fib8() {
  mu_assert("error, fib(8) != 21", r8 == 21);
  return 0;
 }

static char * test_fib9() {
  mu_assert("error, fib(9) != 34", r9 == 34);
  return 0;
 }

static char * test_fib10() {
  mu_assert("error, fib(10) != 55", r10 == 55);
  return 0;
 }

static char * test_fib11() {
  mu_assert("error, fib(11) != 89", r11 == 89);
  return 0;
 }

static char * test_fib12() {
  mu_assert("error, fib(12) != 144", r12 == 144);
  return 0;
 }

static char * test_fib13() {
  mu_assert("error, fib(13) != 233", r13 == 233);
  return 0;
 }

static char * test_fib14() {
  mu_assert("error, fib(14) != 377", r14 == 377);
  return 0;
 }

static char * all_tests() {
  mu_run_test(test_fib1);
  mu_run_test(test_fib2);
  mu_run_test(test_fib3);
  mu_run_test(test_fib4);
  mu_run_test(test_fib5);
  mu_run_test(test_fib6);
  mu_run_test(test_fib7);
  mu_run_test(test_fib8);
  mu_run_test(test_fib9);
  mu_run_test(test_fib10);
  mu_run_test(test_fib11);
  mu_run_test(test_fib12);
  mu_run_test(test_fib13);
  mu_run_test(test_fib14);
  return 0;
}

signed long test_main(signed long n, signed long r, signed long (*fib)(signed long)) {
  n1 = n;
  r14 = r;
  r1 = fib(1);
  r2 = fib(2);
  r3 = fib(3);
  r4 = fib(4);
  r5 = fib(5);
  r6 = fib(6);
  r7 = fib(7);
  r8 = fib(8);
  r9 = fib(9);
  r10 = fib(10);
  r11 = fib(11);
  r12 = fib(12);
  r13 = fib(13);
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
