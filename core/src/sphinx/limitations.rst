.. _limitations:

Limitations of Verification
---------------------------

A goal of Leon is to ensure that proven properties hold in
all program executions so that, for example, verified programs
do not crash and all of the preconditions and postconditions
are true in all executions.
For this to be the case, there needs
to be a precise correspondence between runtime execution
semantics and the semantics used in verification, including
the SMT solvers invoked. 

Below we document several cases where we are aware that the
discrepancy exists and provide suggested workarounds.

Out of Memory Errors
^^^^^^^^^^^^^^^^^^^^

By default Leon assumes that unbounded data types can
be arbitrarily large and that all well-founded recursive
functions have enough stack space to finish their computation.
Thus a verified program may crash at run-time due to:

  * stack overflow
  * heap overflow

Algebraic data types are assumed to be arbitrarily large.
In any given execution, there will be actual bounds on the
total available memory, so the program could crash with out
of memory error when trying to allocate another value of
algebraic data type. 

For a safety critical application you may wish to resort to
tail-recursive programs only, and also write preconditions
and postconditions that enforce a bound on the maximum size
of the data structures that your application
manipulates. For this purpose, you can define size functions
that return `BigInt` data types.

