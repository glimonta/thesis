#ifndef __CHLOE_MALLOC_LIB
#define __CHLOE_MALLOC_LIB

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <inttypes.h>
// TODO: Type of second argument must match integer type of semantics! 
// Insert formal check here! (Problematic, as integer type of semantics comes from generated program)
void * __chloe_malloc(size_t size, int64_t n);

#endif
