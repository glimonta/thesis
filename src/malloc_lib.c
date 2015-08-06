#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <inttypes.h>

intptr_t * __MALLOC(intptr_t size) {
  intptr_t * __ret_malloc = malloc(size);
  if (NULL == __ret_malloc)
    exit(3);
  else
    return __ret_malloc;
}
