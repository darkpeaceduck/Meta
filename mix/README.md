### What is ?
Specialization and partial evaluation for flow chart language

### What Partial Evaluation Is?

Partial evaluation means to fix some variables in the given code
before execution.  With a traditional implementation of a compiler or
an interpreter, all variables are replaced with its value on each
evaluation of that variable.  This is because a variable can change at
any timing.  This is, however, not always true in actual applications.
Almost all of large applications has setting variables and data
variables.  The former is set statically by command-line arguments or
setting files, so they does not change on running.

Partial evaluation is formalized as follows.  Take an source code `s`
and the set of variables `v` in `s`.  `v` can be split into two set
of variables.  One is `Vc`, whose element has a fixed corresponding
value (`c`) before execution.  The other is `Vs`, whose value cannot be
defined statically, vary on the each execution of that part of the
code.  Partial evaluating function `mix` has the following type.

    mix :: source -> constants, configured values -> s*

The output `s*` is a function from data which fix on execution to the
result.

### What Futamura Projection Is?

The basic idea of Futamura projection is to see an interpreter and a
source code as input of `mix` [1].  A source code is a string.  An
interpreter is taken as a 2-ary function.  `mix` takes a 2-ary
operator and some kind of data.

Let's introduce the notion of the universal evaluator to understand
Futamura projection.  The most generalized form of evaluation
is what takes an interpreter of a language, a source code written in
the language, and input data, then outputs the result.  With this
evaluator, one can run any source code if he has an interpreter for
its language (you may think it is obvious, but this characteristic is useful in
application.  See the next section).

    univEval :: interpreter -> source -> input -> output

Futamura projection is equal to partial application on this `univEval`
using `mix` defined in the previous section.  There are 3 kinds of
Futamura projection.  The first projection,

    mix int s  (int: interpreter, s: source)

corresponds to

    univEval int s.

The return value is a function with type `input -> output`.  This is an "executable".

The second is

    mix mix int

which corresponds to

    univEval int.

The type of the return value is `source -> input -> output`, the same as a "compiler".

The third

    mix mix1 mix2   (mix2 is for interpreter, from #2).

is `univEval` itself.  This is an universal compiler generator.

Here, an `executable` and a `compiler` is a bit different from usual
meaning.  An `executable` is not necessarily written in native code.
It just takes data, then outputs.  A `compiler` does not necessarily
generates a native code from a source code.  It takes an source code
and input and outputs the result.

The merit of this approach is that writing an interpreter is usually
easier then writing a compiler from scratch, or using
compiler-compiler with a translator description language [2].

The speed of generated programs is a different question.  It is
obvious that a native code binary is faster than its interpreter
version.  However, as mentioned above, Futamura projection is nothing
to do with the kind of a generated code.  It is up to the
implementation.  In order to see this point in detail, we will see
PyPy, or the RPython toolchain in the next section.
### Want we want

We want implement `mix` for FlowChart Language 
