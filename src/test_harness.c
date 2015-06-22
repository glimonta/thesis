#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <inttypes.h>
#include "hashset.h"

hashset_t discovered;

#define __TEST_HARNESS_DISCOVER(addr, var) hashset_add(discovered, addr); var = addr;


#define __TEST_HARNESS_ASSERT_EQ(var, val) (var != val) ? printf("%"PRIdPTR" != %"PRIdPTR"\n", var, val) : printf("S'all good man!\n") ;

#define __TEST_HARNESS_ASSERT_EQ_NULL(var) (&var != NULL) ? printf("%p != NULL\n", (void*)var) : printf("S'all good man!\n") ;

#define __TEST_HARNESS_ASSERT_EQ_PTR(var, val) (var != val) ? printf("%p != %p\n", (void*)var, (void*)val) : printf("S'all good man!\n") ;

int main () {
  discovered = hashset_create();

  intptr_t n = 42;
  intptr_t m = malloc(sizeof(intptr_t));
  *(intptr_t *)m = 42;
  intptr_t o = m;
  intptr_t p = malloc(sizeof(intptr_t));


  __TEST_HARNESS_ASSERT_EQ(n, 42);
  __TEST_HARNESS_ASSERT_EQ(n, 21);
  __TEST_HARNESS_ASSERT_EQ_NULL(n);
  __TEST_HARNESS_ASSERT_EQ_NULL(m);
  __TEST_HARNESS_ASSERT_EQ_PTR(m, o);
  __TEST_HARNESS_ASSERT_EQ_PTR(m, p);
  __TEST_HARNESS_FOLLOW(m);
  __TEST_HARNESS_ASSERT_EQ(m, 42);
  __TEST_HARNESS_ASSERT_EQ(m, 21);

  intptr_t x1, x2;

  __TEST_HARNESS_DISCOVER(m, x1);
  __TEST_HARNESS_DISCOVER(p, x2);

  int r = hashset_is_member(discovered, m);
  int r2 = hashset_is_member(discovered, p);
  int r3 = hashset_is_member(discovered, o);

  printf("%d,%d,%d\n", r, r2, r3);

}
