COPTS = -Wall -Wextra -ggdb -D_GNU_SOURCE
.PHONY: all clean

all: bubblesort count fact fib mergesort min occurs quicksort selection strlen

bubblesort: bubblesort.c; gcc $(COPTS) -o $@ $^
count:      count.c;      gcc $(COPTS) -o $@ $^
fact:       fact.c;       gcc $(COPTS) -o $@ $^
fib:        fib.c;        gcc $(COPTS) -o $@ $^
mergesort:  mergesort.c;  gcc $(COPTS) -o $@ $^
min:        min.c;        gcc $(COPTS) -o $@ $^
occurs:     occurs.c;     gcc $(COPTS) -o $@ $^
quicksort:  quicksort.c;  gcc $(COPTS) -o $@ $^
selection:  selection.c;  gcc $(COPTS) -o $@ $^
strlen:     strlen.c;     gcc $(COPTS) -o $@ $^

clean: ; rm -f ./*.o bubblesort count fact fib mergesort min occurs quicksort selection strlen
