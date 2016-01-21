#!/bin/bash

TEST_NAMES=`find -maxdepth 1 -name '*_test' -type f -executable`

for test_name in ${TEST_NAMES}
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
  3) echo -e "\e[31mMemory allocation error\e[39m ocurred in execution of ${test_name}";;
  126) echo -e "\e[31mError\e[39m (command invoked cannot execute) occurred in the execution of ${test_name}";;
  127) echo -e "\e[31mError\e[39m (command not found) occurred in the execution of ${test_name}";;
  128) echo -e "\e[31mError\e[39m (invalid argument given to exit) occurred in the execution of ${test_name}";;
  130) echo -e "\e[31mError\e[39m (program terminated by Ctrl+C) occurred in the execution of ${test_name}";;
  139) echo -e "\e[31mSegmentation fault\e[39m ocurred in execution of ${test_name}";;
  *) echo ${res};;
  esac
fi
done
