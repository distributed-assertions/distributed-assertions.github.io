# λProlog Bridge to DAMF

&lambda;Prolog is a logic programming language that extends Prolog in a number
of ways. In particular, it has a built-in and declarative treatment of
term-level bindings.  For more about &lambda;Prolog, see:

- The [&lambda;Prolog home page](https://www.lix.polytechnique.fr/~dale/lProlog/)
- The book [Programming with Higher-Order Logic](https://sites.google.com/site/proghol/) by D. Miller and G. Nadathur describes the logic, design, and applications for &lambda;Prolog.

There are two main implementations of &lambda;Prolog.

- [ELPI](https://github.com/LPCIC/elpi/): an embeddable λProlog interpreter.
  [Version 1.16.7](https://github.com/LPCIC/elpi/) was released on 20 October 2022.
- [Teyjus](https://github.com/teyjus/teyjus) compiler of λProlog.
  [Version 2.1.1](https://github.com/teyjus/teyjus/releases) was released on 7 February 2023.

The &lambda;Prolog code for producing JSON objects suitable for Dispatch are in
[this folder][lProlog-code].

[lProlog-code]: https://github.com/distributed-assertions/distributed-assertions.github.io/tree/main/docs/assets/lProlog

The following description assumes that one is using the Teyjus compiler for
&lambda;Prolog and that all the .mod files are compiled and linked.

The process for generating JSON involves the following additional files, all
based on a common name, here written as `FILE`.  There are three input files
(the first three described here) and one output file.

- `FILE.sig` - the kind/type declarations needed
- `FILE.mod` - find here the lambda Prolog clauses
- `FILE.goals` - these are the named goals that will be printed as theorems.
- `FILE.json`  - the output file for dispatch

Currently, the specific instructions to use this code are the following:

- Add "accumlate FILE." to `harness.mod`
- Add "accum_sig FILE." to `harness.sig`
- Run both `tjcc` and `tjsim` on `FILE`, eg: `> tjcc arith ; tjlink arith`
- Make sure that FILE.goals has no blank lines.
- Compiler and run:
  ```bash
  tjcc harness ; tjlink harness ; tjsim harness
  ```
- Issue the goal: `json FILE`.
- The result is `FILE.json`.

Toplevel command in `tjsim`, once harness and associated modules have been
compiled and loaded:

```
> tjsim harness
?- json "File".
```
