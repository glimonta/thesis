#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <inttypes.h>
#include "hashset.h"

hashset_t discovered;
int num_tests = 0;
int passed = 0;
int failed = 0;

#define __TEST_HARNESS_DISCOVER(addr, var) hashset_add(discovered, addr); var = addr;

#define __TEST_HARNESS_ASSERT_EQ(var, val) ++num_tests; (var != val) ? ++failed : ++passed;

#define __TEST_HARNESS_ASSERT_EQ_NULL(var) ++num_tests; (var != NULL) ? ++failed : ++passed;

#define __TEST_HARNESS_ASSERT_EQ_PTR(var, val) ++num_tests; (var != val) ? ++failed : ++passed;
