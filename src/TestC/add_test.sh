#!/bin/bash

sed '$d' bubblesort_gen.c > bubblesort.c
echo $'  test_main(a,n,bubblesort);\n}' >> bubblesort.c

sed '$d' count_gen.c > count.c
echo $'  test_main(a,n,foo,bar,baz,count);\n}' >> count.c

sed '$d' fact_gen.c > fact.c
echo $'  test_main(n,r,fact);\n}' >> fact.c

sed '$d' fib_gen.c > fib.c
echo $'  test_main(n,r,fib);\n}' >> fib.c

sed '$d' mergesort_gen.c > mergesort.c
echo $'  test_main(a,n,mergesort);\n}' >> mergesort.c

sed '$d' min_gen.c > min.c
echo $'  test_main(a,n,m,min);\n}' >> min.c
