COPTS = -Wall -Wextra -ggdb -D_GNU_SOURCE
HASH = ../hashset.h ../hashset.c
TEST = ../test_harness.h
.PHONY: all clean

all: bubblesort bubblesort_test count count_test fact fact_test fib fib_test mergesort mergesort_test min min_test occurs occurs_test quicksort quicksort_test selection selection_test strlen strlen_test plus plus_test subst subst_test outer_scope outer_scope_test local_scope local_scope_test global_scope global_scope_test global_scope2 global_scope2_test mod mod_test div div_test mult mult_test less less_test and and_test or or_test not not_test eq eq_test new new_test deref deref_test

# Executables for the regular programs.
bubblesort:    bubblesort.c;    gcc $(COPTS) -o $@ $^
count:         count.c;         gcc $(COPTS) -o $@ $^
fact:          fact.c;          gcc $(COPTS) -o $@ $^
fib:           fib.c;           gcc $(COPTS) -o $@ $^
mergesort:     mergesort.c;     gcc $(COPTS) -o $@ $^
min:           min.c;           gcc $(COPTS) -o $@ $^
occurs:        occurs.c;        gcc $(COPTS) -o $@ $^
quicksort:     quicksort.c;     gcc $(COPTS) -o $@ $^
selection:     selection.c;     gcc $(COPTS) -o $@ $^
strlen:        strlen.c;        gcc $(COPTS) -o $@ $^
plus:          plus.c;          gcc $(COPTS) -o $@ $^
subst:         subst.c;         gcc $(COPTS) -o $@ $^
outer_scope:   outer_scope.c;   gcc $(COPTS) -o $@ $^
local_scope:   local_scope.c;   gcc $(COPTS) -o $@ $^
global_scope:  global_scope.c;  gcc $(COPTS) -o $@ $^
global_scope2: global_scope2.c; gcc $(COPTS) -o $@ $^
mod:           mod.c;           gcc $(COPTS) -o $@ $^
div:           div.c;           gcc $(COPTS) -o $@ $^
mult:          mult.c;          gcc $(COPTS) -o $@ $^
less:          less.c;          gcc $(COPTS) -o $@ $^
and:           and.c;           gcc $(COPTS) -o $@ $^
or:            or.c;            gcc $(COPTS) -o $@ $^
not:           not.c;           gcc $(COPTS) -o $@ $^
eq:            eq.c;            gcc $(COPTS) -o $@ $^
new:           new.c;           gcc $(COPTS) -o $@ $^
deref:         deref.c;         gcc $(COPTS) -o $@ $^

# Executables for the programs that include the tests.
bubblesort_test:    bubblesort_test.c;    gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
count_test:         count_test.c;         gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
fact_test:          fact_test.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
fib_test:           fib_test.c;           gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
mergesort_test:     mergesort_test.c;     gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
min_test:           min_test.c;           gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
occurs_test:        occurs_test.c;        gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
quicksort_test:     quicksort_test.c;     gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
selection_test:     selection_test.c;     gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
strlen_test:        strlen_test.c;        gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
plus_test:          plus_test.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
subst_test:         subst_test.c;         gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
outer_scope_test:   outer_scope_test.c;   gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
local_scope_test:   local_scope_test.c;   gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
global_scope_test:  global_scope_test.c;  gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
global_scope2_test: global_scope2_test.c; gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
mod_test:           mod_test.c;           gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
div_test:           div_test.c;           gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
mult_test:          mult_test.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
less_test:          less_test.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
and_test:           and_test.c;           gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
or_test:            or_test.c;            gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
not_test:           not_test.c;           gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
eq_test:            eq_test.c;            gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
new_test:           new_test.c;           gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)
deref_test:         deref_test.c;         gcc $(COPTS) -o $@ $^ $(TEST) $(HASH)

clean: ; rm -f ./*.o bubblesort count fact fib mergesort min occurs quicksort selection strlen bubblesort_test count_test fact_test fib_test mergesort_test min_test occurs_test quicksort_test selection_test strlen_test plus plus_test subst subst_test outer_scope outer_scope_test local_scope local_scope_test global_scope global_scope_test global_scope2 global_scope2_test mod mod_test div div_test mult mult_test less less_test and and_test or or_test not not_test eq eq_test new new_test deref deref_test
