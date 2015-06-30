Thesis Outline
================

1. Introduction

    1.1. Theoretical Background

            1.1.1. What is the semantics of a programming language

                1.1.1.1. Definition

                1.1.1.2. Types of semantics

            1.1.2. Definition of the language used in this work

                1.1.2.1. Syntax

                1.1.2.1. Static semantics

    1.2 Previous and related work

2. Problem statement

    (I am still not sure on how to split this into parts.)

    2.1. Introduction of the problem

3. Design

    3.1. Introduction of Isabelle as the tool used to solve the problem

    3.2. Semantics

            3.2.1. Expressions

                3.2.1.1. Memory

                3.2.1.2. Types

                    3.2.1.2.1. Addresses

                    3.2.1.2.1. Integers

            3.2.2. Evaluation of expressions

            3.2.3. Commands

                3.2.3.1. Functions

                3.2.3.2. Programs in the language

    3.3. Restrictions in the target architecture and other design decisions taken

    3.4. Execution environment

            3.4.1. States

                3.4.1.1. Valuations

                3.4.1.2. Stack

                3.4.1.2.1 Procedure tables

    3.5. Small step semantics

            3.5.1. CFG

            3.5.2. Small step semantics definition

    3.6. Interpreter

            3.6.1. Single step

            3.6.2. Execution and interpretation

            3.6.3. Correctness

4. Pretty printer

    4.1. Pretty printing of values

    4.2. Pretty printing of memory

    4.3. Pretty printing of expressions

    4.4. Pretty printing of commands

    4.5. Pretty printing of declarations

    4.6. Pretty printing of states

    4.7. Pretty printing of a program

    4.8. Exporting C code

5. Testing

    5.1. Description of the test harness created in Isabelle

    5.2. Description of the supporting set of macros in C

    5.3. Types of tests

            5.3.1. Equality of final states

  Final state of memory and global variables yielded by Isabelle interpreter is the same as the one yielded by the generated, compiled and run C program.

                5.3.1.1. Generation of tests

                    5.3.1.1.1. Integer values

                    5.3.1.1.2. Pointers

                        5.3.1.1.2.1. Isabelle representation of the heap vs. the real C heap

                5.3.1.2. Generation of code that tests itself
                    using the test harness and the C macros

            5.3.2. Verification that the semantics of the generated program is the same as the one in the language semantics

                5.3.2.1. Properties that are covered by the tests

6. Results

7. Conclusion
