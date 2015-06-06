#!/bin/bash

clear

make clean && make

clear

bubblestr=`./bubblesort`
countstr=`./count`
factstr=`./fact`
fibstr=`./fib`
mergesortstr=`./mergesort`
minstr=`./min`
occursstr=`./occurs`
quicksortstr=`./quicksort`
selectionstr=`./selection`
strlenstr=`./strlen`

if [ "$bubblestr" == $'-26,1,1,38,44,54,60,80,84,92' ]; then tput setaf 2; echo "bubblesort works!"; else tput setaf 1; echo "bubblesort fails!"; fi
if [ "$countstr" == $'44,98,44,44,54,1,92,84,44,44\nthe number 5 occurs 0 times, the number 84 occurs 1 times, the number 44 occurs 5 times.' ]; then tput setaf 2; echo "count works!"; else tput setaf 1; echo "count fails!";  fi
if [ "$factstr" == $'the factorial of number 5 is 120.' ]; then tput setaf 2; echo "factorial works!"; else tput setaf 1; echo "factorial fails!"; fi
if [ "$fibstr" == $'the fibonacci number of 14 is 377.' ]; then tput setaf 2; echo "fibonacci works!"; else tput setaf 1; echo "fibonacci fails!"; fi
if [ "$mergesortstr" == $'1,26,38,44,54,60,80,84,92,98' ]; then tput setaf 2; echo "mergesort works!"; else tput setaf 1; echo "mergesort fails!"; fi
if [ "$minstr" == $'44,98,60,26,54,1,92,84,38,80\nthe minimum of the array is 1.' ]; tput setaf 2; then echo "min works!"; else tput setaf 1; echo "min fails!"; fi
if [ "$occursstr" == $'44,98,60,26,54,1,92,84,38,80\ndoes number 5 occur?: no, does number 84 occur?: yes.' ]; then tput setaf 2; echo "occurs works!"; else tput setaf 1; echo "occurs fails!"; fi
if [ "$quicksortstr" == $'0,1,2,4,31,65,83,92,99,782' ]; then tput setaf 2; echo "quicksort works!"; else tput setaf 1; echo "quicksort fails!"; fi
if [ "$selectionstr" == $'1,26,38,44,54,60,80,84,92,98' ]; then tput setaf 2; echo "selection works!"; else tput setaf 1; echo "selection fails!"; fi
if [ "$strlenstr" == $'1,2,3,4,5,0\nthe length of the array is: 5.' ]; then tput setaf 2; echo "strlen works!"; else tput setaf 1; echo "strlen fails!"; fi
