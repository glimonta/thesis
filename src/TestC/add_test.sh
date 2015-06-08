#!/bin/bash

sed '$d' bubblesort_gen.c > bubblesort.c
echo $'  test_main(n,a);\n}' >> bubblesort.c

sed '$d' count_gen.c > count.c
echo $'  test_main(n,a,foo,bar,baz);\n}' >> count.c

sed '$d' fact_gen.c > fact.c
echo $'  test_main(n,r);\n}' >> fact.c

sed '$d' fib_gen.c > fib.c
echo $'  test_main(n,r,fib);\n}' >> fib.c

sed '$d' mergesort_gen.c > mergesort.c
echo $'  test_main(n,a);\n}' >> mergesort.c
