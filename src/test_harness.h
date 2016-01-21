#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <inttypes.h>
#include "hashset.h"

hashset_t __test_harness_discovered;
int __test_harness_num_tests = 0;
int __test_harness_passed = 0;
int __test_harness_failed = 0;

#define __TEST_HARNESS_DISCOVER(addr, var) if (hashset_add(__test_harness_discovered, addr)<=0) ++__test_harness_failed; var = addr;

#define __TEST_HARNESS_ASSERT_EQ(var, val) ++__test_harness_num_tests; (var != val) ? ++__test_harness_failed : ++__test_harness_passed;

#define __TEST_HARNESS_ASSERT_EQ_NULL(var) ++__test_harness_num_tests; (var != NULL) ? ++__test_harness_failed : ++__test_harness_passed;

#define __TEST_HARNESS_ASSERT_EQ_PTR(var, val) ++__test_harness_num_tests; (var != val) ? ++__test_harness_failed : ++__test_harness_passed;
