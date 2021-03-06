COPTS = -Wall -Wextra -ggdb -D_GNU_SOURCE
HASH = ../hashset.h ../hashset.c
TEST = ../test_harness.h
MALLOC = ../malloc_lib.h ../malloc_lib.c
GCC = gcc
.PHONY: all clean

SOURCES = $(wildcard *.c)
BINARIES = $(SOURCES:.c=)

%: %.c $(TEST) $(HASH) $(MALLOC)
	gcc $(COPTS) -o $@ $^ 


all: $(BINARIES)

clean:
	rm -rf $(BINARIES)

# all: basic_ops basic_ops_test bubblesort bubblesort_test count count_test fact fact_test fib fib_test mergesort mergesort_test min min_test occurs occurs_test quicksort quicksort_test selection selection_test strlen strlen_test plus plus_test subst subst_test outer_scope outer_scope_test local_scope local_scope_test global_scope global_scope_test global_scope2 global_scope2_test mod mod_test div div_test mult mult_test less less_test and and_test or or_test not not_test eq eq_test new new_test deref deref_test while while_test returnv returnv_test linked_list linked_list_test cyclic_linked_list cyclic_linked_list_test
# 
# # Executables for the regular programs.
# basic_ops:          basic_ops.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# bubblesort:         bubblesort.c;         gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# count:              count.c;              gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# fact:               fact.c;               gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# fib:                fib.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# mergesort:          mergesort.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# min:                min.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# occurs:             occurs.c;             gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# quicksort:          quicksort.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# selection:          selection.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# strlen:             strlen.c;             gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# plus:               plus.c;               gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# subst:              subst.c;              gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# outer_scope:        outer_scope.c;        gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# local_scope:        local_scope.c;        gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# global_scope:       global_scope.c;       gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# global_scope2:      global_scope2.c;      gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# mod:                mod.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# div:                div.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# mult:               mult.c;               gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# less:               less.c;               gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# and:                and.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# or:                 or.c;                 gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# not:                not.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# eq:                 eq.c;                 gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# new:                new.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# deref:              deref.c;              gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# while:              while.c;              gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# returnv:            returnv.c;            gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# linked_list:        linked_list.c;        gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# cyclic_linked_list: cyclic_linked_list.c; gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# 
# # Executables for the programs that include the tests.
# basic_ops_test:          basic_ops_test.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# bubblesort_test:         bubblesort_test.c;         gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# count_test:              count_test.c;              gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# fact_test:               fact_test.c;               gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# fib_test:                fib_test.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# mergesort_test:          mergesort_test.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# min_test:                min_test.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# occurs_test:             occurs_test.c;             gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# quicksort_test:          quicksort_test.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# selection_test:          selection_test.c;          gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# strlen_test:             strlen_test.c;             gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# plus_test:               plus_test.c;               gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# subst_test:              subst_test.c;              gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# outer_scope_test:        outer_scope_test.c;        gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# local_scope_test:        local_scope_test.c;        gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# global_scope_test:       global_scope_test.c;       gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# global_scope2_test:      global_scope2_test.c;      gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# mod_test:                mod_test.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# div_test:                div_test.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# mult_test:               mult_test.c;               gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# less_test:               less_test.c;               gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# and_test:                and_test.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# or_test:                 or_test.c;                 gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# not_test:                not_test.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# eq_test:                 eq_test.c;                 gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# new_test:                new_test.c;                gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# deref_test:              deref_test.c;              gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# while_test:              while_test.c;              gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# returnv_test:            returnv_test.c;            gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# linked_list_test:        linked_list_test.c;        gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# cyclic_linked_list_test: cyclic_linked_list_test.c; gcc $(COPTS) -o $@ $^ $(TEST) $(HASH) $(MALLOC)
# 
# clean: ; rm -f ./*.o bubblesort count fact fib mergesort min occurs quicksort selection strlen bubblesort_test count_test fact_test fib_test mergesort_test min_test occurs_test quicksort_test selection_test strlen_test plus plus_test subst subst_test outer_scope outer_scope_test local_scope local_scope_test global_scope global_scope_test global_scope2 global_scope2_test mod mod_test div div_test mult mult_test less less_test and and_test or or_test not not_test eq eq_test new new_test deref deref_test while while_test returnv returnv_test linked_list linked_list_test cyclic_linked_list cyclic_linked_list_test
