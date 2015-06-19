#include <limits.h>
#include <stdint.h>
#include <stdio.h>

#if ( LONG_MIN != -9223372036854775808U )
  #error ("Assertion LONG_MIN == -9223372036854775808 failed")
#endif
#if ( LONG_MAX != 9223372036854775807 )
  #error ("Assertion LONG_MAX == 9223372036854775807 failed")
#endif

#ifndef INTPTR_MIN 
  #error "Not Defined"
#endif

#if (INTPTR_MIN != LONG_MIN)
  #error
#endif

#if (INTPTR_MAX != LONG_MAX)
  #error
#endif

intptr_t x--

void main() {
  printf ("%d", SCHAR_MIN);
   
  
  
}

