# Incorrect Tests

## Tests on expressions

* Const
    + overflow1_const: overflow when trying to create a constant with a value bigger than INT_MAX.
    + overflow2_const: overflow when trying to create a constant with a value bigger than INT_MIN.
* Null
* V x
    + non_declared: try to access a variable that is not declared.
    + non_init: try to use a variable that is not initialized.
    + wrong_scope: try to use in the global scope a variable of local scope.
    + reserved_keywords: try to use the reserved keywords as variable names.
* Plus i1 i2
    + overflow1_plus: overflow when the value of the addition is bigger than INT_MAX.
    + overflow2_plus: overflow when the value of the addition is smaller than INT_MIN.
    + address_plus: addition of two addresses.
    + integer_address_plus: adittion of an integer and an address.
    + integer_null_plus: addition of an integer and a NullVal.
    + address_null_plus: addition of an address and a NullVal.
    + null_integer_plus: addition of a NullVal and an integer.
    + null_address_plus: addition of a NullVal and an address.
* Subst
    + overflow1_subst: overflow when the value of the substraction is bigger than INT_MAX.
    + overflow2_subst: overflow when the value of the substraction is smaller than INT_MIN.
    + address_subst: substraction of two addresses.
    + integer_address_subst: substraction of an integer and an address.
    + integer_null_subst: substraction of an integer and a NullVal.
    + address_null_subst: substraction of an address and a NullVal.
    + null_integer_subst: substraction of a NullVal and an integer.
    + null_address_subst: substraction of a NullVal and an address.
* Minus
    + overflow1_minus: overflow when the value of the unary minus operand is bigger than INT_MAX.
    + overflow2_minus: overflow when the value of the unary minus operand is smaller than INT_MIN.
    + address_minus: try to do unary minus operation on an address.
    + null_minus: try to do unary minus operation on a NullVal.
* Mod
    + overflow1_mod: overflow when the value of the modulo is bigger than INT_MAX.
    + overflow2_mod: overflow when the value of the modulo is smaller than INT_MIN.
    + zero_mod: the second operand of the modulo operation is zero.
    + address_mod: modulo of two addresses.
    + integer_address_mod: modulo of an integer and an address.
    + address_integer_mod: modulo of an address and an integer.
    + integer_null_mod: modulo of an integer and a NullVal.
    + address_null_mod: modulo of an address and a NullVal.
    + null_integer_mod: modulo of a NullVal and an integer.
    + null_address_mod: modulo of a NullVal and an address.
* Div
    + overflow1_div: overflow when the value of the division is bigger than INT_MAX.
    + overflow2_div: overflow when the value of the division is smaller than INT_MIN.
    + zero_div: the second operand of the division operation is zero.
    + address_div: division of two addresses.
    + integer_address_div: division of an integer and an address.
    + address_integer_div: division of an address and an integer.
    + integer_null_div: division of an integer and a NullVal.
    + address_null_div: division of an address and a NullVal.
    + null_integer_div: division of a NullVal and an integer.
    + null_address_div: division of a NullVal and an address.
* Mult
    + overflow1_mult: overflow when the value of the multiplication is bigger than INT_MAX.
    + overflow2_mult: overflow when the value of the multiplication is smaller than INT_MIN.
    + address_mult: multiplication of two addresses.
    + integer_address_mult: adittion of an integer and an address.
    + address_integer_mult: multiplication of an address and an integer.
    + integer_null_mult: multiplication of an integer and a NullVal.
    + address_null_mult: multiplication of an address and a NullVal.
    + null_integer_mult: multiplication of a NullVal and an integer.
    + null_address_mult: multiplication of a NullVal and an address.
* Less
    + address_less: less than operation between two addresses.
    + integer_address_less: adittion between an integer and an address.
    + address_integer_less: less than operation between an address and an integer.
    + integer_null_less: less than operation between an integer and a NullVal.
    + address_null_less: less than operation between an address and a NullVal.
    + null_integer_less: less than operation between a NullVal and an integer.
    + null_address_less: less than operation between a NullVal and an address.
* Not
    + address_not: try to do not operation on an address.
    + null_not: try to do not operation on a NullVal.
* And
    + address_and: and operation between two addresses.
    + integer_address_and: adittion between an integer and an address.
    + address_integer_and: and operation between an address and an integer.
    + integer_null_and: and operation between an integer and a NullVal.
    + address_null_and: and operation between an address and a NullVal.
    + null_integer_and: and operation between a NullVal and an integer.
    + null_address_and: and operation between a NullVal and an address.
* Or
    + address_or: or operation between two addresses.
    + integer_address_or: adittion between an integer and an address.
    + address_integer_or: or operation between an address and an integer.
    + integer_null_or: or operation between an integer and a NullVal.
    + address_null_or: or operation between an address and a NullVal.
    + null_integer_or: or operation between a NullVal and an integer.
    + null_address_or: or operation between a NullVal and an address.
* Eq
    + integer_address_eq: adittion between an integer equality an address.
    + address_integer_eq: equality operation between an address and an integer.
    + integer_null_eq: equality operation between an integer and a NullVal.
    + address_null_eq: equality operation between an address and a NullVal.
    + null_integer_eq: equality operation between a NullVal and an integer.
    + null_address_eq: equality operation between a NullVal and an address.
* New
    + zero_new: try to allocate a new block of size zero.
    + negative_new: try to allocate a new block of negative size.
    + address_new: try to allocate a new block with an address.
    + null_new: try to allocate a new block with a NullVal.
* Deref (*)
    + integer_deref: try to dereference an integer value.
    + null_deref: try to dereference a NullVal.
    + invalid_addr_deref: try to dereference an invalid address value.
* Ref (&)
    + integer_ref: try to reference a value that results in an integer.
      this one makes no sense because you cannot reference an integer syntactically.
    + null_ref: try to reference a value that results in a NullVal.
      this one makes no sense because you cannot reference an NullVal syntactically.
* Index (e[e])
    + integer_index: try to index with two integers.
    + address_index: try to index with two addresses.
    + null_index1: try to index with NullVal as the first operator.
    + null_index2: try to index with NullVal as the second operator.
* Derefl
    + integer_derefl: try to dereference an integer value.
    + null_derefl: try to dereference a NullVal.
    + invalid_addr_derefl: try to dereference an invalid address value.
* Indexl
    + integer_indexl: try to index with two integers.
    + address_indexl: try to index with two addresses.
    + null_indexl1: try to index with NullVal as the first operator.
    + null_indexl2: try to index with NullVal as the second operator.

## Test on Commands

* Assignl
    + already kind of proved with the expressions.
* Assign
    + already kind of proved with the expressions.
* While
* Free
    + integer_free: try to free with an integer value.
      makes no sense, free takes an lexp.
    + null_free: try to free with a NullVal.
      makes no sense, free takes an lexp.
    + invalid_free: try to free an invalid address.
* Returnv
    + variable_returnv: try to return void in a function with variable return value.
    + address_returnv: try to return void in a function with address return value.
* Callfunl
    + many_args_callfunl: call a function with more arguments than the parameters.
    + few_args_callfunl: call a function with fewer arguments than the parameters.
    + no_args_callfunl: call a function that has parameters with no arguments.
* Callfun
    + many_args_callfun: call a function with more arguments than the parameters.
    + few_args_callfun: call a function with fewer arguments than the parameters.
    + no_args_callfun: call a function that has parameters with no arguments.
* Callfunv
    + many_args_callfunv: call a function with more arguments than the parameters.
    + few_args_callfunv: call a function with fewer arguments than the parameters.
    + no_args_callfunv: call a function that has parameters with no arguments.

## Other tests

* Non-Termination
    + non_termination_while: while true.
      this never ends executing, what to do?
* Off-by-one


# Correct Tests

## Test on expressions

* Const
* Null
* V x
    + outer_scope: use in the context of a local procedure, a variable that is declared in the global scope.
    + local_scope: use in the context of a local procedure a variable declared in that same scope.
    + global_scope: use in the context of the global scope a variable declared in the global scope.
    + global_scope2: use in the context of a nested function call a global variable
* Plus
    + plus: Correct addition of two integers and an integer and an address.
* Subst
    + subst: Correct substraction of two integer and an integer and an address.
* Minus
    + minus: Correct minus operation on a integer value.
* Mod
    + mod: Correct modulo operation on integer values, show truncation towards zero works.
* Div
    + div: Correct division operation on integer values, show truncation towards zero works.
* Mult
    + mult: Correct multiplication on integer values.
* Less
    + less: Correct values when comparing (True and False).
* Not
    + not: Correct values for the operation.
* And
    + and: Correct evaluations, demostrantion of short-circuit evaluation.
* Or
    + or: Correct evaluations, demostrantion of short-circuit evaluation.
* Eq
    + eq: equality between two integers and between two addresses, show correct values.
* New
    + new: try to allocate new blocks of different length.
* Deref
    + deref: allocate a new block of memory, initialize it and dereference it to compare the values.
* Ref
    + ref: allocate a new block of memory, initialize it and reference it to compare the values.
* Index
    + index: allocate a new block of memory, initialize it and index it to compare the values.
* Derefl
    + deref: allocate a new block of memory, initialize it and dereference it to compare the addresses.
* Indexl
    + ref: allocate a new block of memory, initialize it and reference it to compare the addresses.


## Test on Commands

* Assignl
    + assignl: Assignments to memory are made correctly.
* Assign
    + assign: Assignments to variables are made correctly.
* If
    + if: taking the true branch and taking the false branch.
* While
    + while: cycle that executes a definite amout of times, cycle that is not executed at all.
    + returnv: even if a void function has no return then it will return when reaching end of control.
      Return from a void function.
* Callfunl
    + callfunl: check that the returned value is where it should be.
* Callfun
    + callfun: check that the returned value is where it should be.

## Example programs

* Bubblesort
* Count
* Factorial
* Fibonacci
* Mergesort
* Minimum
* Occurs
* Quicksort
* Selectionsort
* StrLength

* Binary trees (array)
* Lists
* Ordered list
* Binary search trees
