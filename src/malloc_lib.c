#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <inttypes.h>
#include "malloc_lib.h"

void * __chloe_malloc(size_t size, int64_t n) {
  if (n<=0) exit(3);
  void *res = calloc((size_t)n, size);
  if (res==0) exit(3);
  return res;
}

