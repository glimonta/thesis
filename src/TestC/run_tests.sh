#!/bin/bash

TEST_NAMES=(bubblesort_test count_test fact_test fib_test
  mergesort_test min_test occurs_test quicksort_test selection_test
  strlen_test plus_test subst_test outer_scope_test local_scope_test
  global_scope_test global_scope2_test mod_test div_test mult_test
  less_test and_test or_test not_test eq_test new_test deref_test
  while_test returnv_test linked_list_test cyclic_linked_list_test)

trap 'if [[ $? -eq 139 ]]; then echo "segfault !"; fi' CHLD

for test_name in ${TEST_NAMES[@]}
do
  res=$(./${test_name});
  ret=$?

if [[ ${res} == Failed* ]];
  then
    echo -e "\e[31mFAILED: \e[39m${res}"
else
  case ${ret} in

  1) echo -e "\e[31mError\e[39m (general error) occurred in the execution of ${test_name}";;
  2) echo -e "\e[31mError\e[39m (misuse of shell builtins) occurred in the execution of ${test_name}";;
  3)  echo -e "\e[31mMemory allocation error\e[39m ocurred in execution of ${test_name}";;
  126) echo -e "\e[31mError\e[39m (command invoked cannot execute) occurred in the execution of ${test_name}";;
  127) echo -e "\e[31mError\e[39m (command not found) occurred in the execution of ${test_name}";;
  128) echo -e "\e[31mError\e[39m (invalid argument given to exit) occurred in the execution of ${test_name}";;
  130) echo -e "\e[31mError\e[39m (program terminated by Ctrl+C) occurred in the execution of ${test_name}";;
  139)  echo -e "\e[31mSegmentation fault\e[39m ocurred in execution of ${test_name}";;
  *) echo ${res};;
  esac
fi
done
