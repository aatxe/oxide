# Tested Semantics

We set out at the onset to solve a particular problem --- there is no high-level
specification of the Rust programming language and its borrowchecker. If there
were, this would be the point where we might present a proof that every
expression that type checks in Oxide also type checks in Rust and vice versa.
Since doing that is not possible, we developed a _tested semantics_ for Oxide
typechecking. This repository contains an implementation of our Oxide type-checking
algorithm, OxideTC, alongside a compiler, called Reducer, from a subset of Rust
(with a small number of additional annotations) to Oxide. In addition to the
features described by the formalization, our implementation supports Rust's
structs by treating them as tagged tuples or records. The combined
Reducer-OxideTC tooling has allowed us to use tests from the official borrow
checker (borrowck) and non-lexical lifetime (nll) test suites to validate Oxide's 
faithfulness as a model of Rust against its implementation, rustc. The results
of this testing is summarized in the table presented in the paper.

For the 208 passing tests, we can compile the test case into Oxide with
Reducer and then use OxideTC to either successfully type check the
program or to produce a type error. We compare this type checking result to the
expected behavior according to the rustc test suite. All 208 tests either type
check when rustc does so, or produce an error corresponding to the error
produced by rustc.

The remaining 407 tests were taken out of consideration on the basis of being
out-of-scope for this work. There were 20 categories for exclusion, the majority
of which had fewer than 10 applicable tests. The table includes the
6 largest categories: (1)~heap allocation, (2)~out-of-scope libraries,
(3)~enumerations, (4)~statics and constants, (5)~traits, and (6)~uninitialized
variables. One specialized category (multithreading) was folded into
out-of-scope libraries in this table, with the miscellaneous column aggregating
the remaining smaller categories: control flow, casting, first-class
constructors, compiler internals dumping, function mutability, inline assembly,
macros, slice patterns, two-phase borrows, uninitialized variables, universal
function-call syntax, unsafe, and variable mutability.

Combined, heap allocation and out-of-scope libraries (of which the former is a
specialization of the latter) make up for the largest excluded category with 103
tests, and is the most immediate avenue for future work. The next largest
category, traits, accounts for 93 tests. Though the trait system is in some ways
novel, the bulk of its design is rooted in the work on Haskell typeclasses and
their extensions. As such, we feel that they are not an _essential_ part of
Rust, though exploring the particularities of their design may be a fruitful
avenue for future work on typeclasses. We are working on extending our
implementation with sums to support enumerations. Many of the other categories
describe features (e.g., macros, control flow, casting, first-class constructors,
statics, and constants) that are well-studied in the programming languages
literature, and in which we believe Rust has made relatively standard design choices.

The last issue to discuss involving the tested semantics is the aforementioned
annotation burden. This burden comes directly out of the syntactic differences
between Oxide and Rust as seen in the paper, and so are fairly minor. The
most immediately apparent need is to provide a origin annotation on borrow
expressions, which we handle using Rust's compiler annotation support. In our
tests, a borrow expression like `&'a uniq x` appears as `#[lft="a"] &mut x`.
However, we reduce the need for this by automatically generating a fresh local
origin for borrow expressions without an annotation. This suffices for the
majority of expressions without change. Relatedly, one might also expect to see
the introduction of \oxkey{letprov} throughout. To alleviate the need for this,
our implementation automatically binds free origin at the beginning of each
function body.

The other main change we had to make relates to the use of explicit environment
polymorphism in Oxide. In Rust, every closure has a unique type without a syntax
for writing it down. To work with higher-order functions, these closures
implement one of three special language-defined traits (`Fn`, `FnMut`, and `FnOnce`)
which can be used as bounds in higher-order functions. We compile the use of these
trait bounds to environment polymorphism in a straight-forward manner (turning
instances of the same `Fn`-bound polymorphic type into uses of function types with
the same environment variable), but need to introduce a way of writing down which
environment to use at instantiation time. We use a compiler annotation
(`#[envs(c1, ..., cn)]`) on applications which says to instantiate the environment
variables with the captured environments of the types of these bindings. If the
bindings are unbound or not at a function type, we produce an error indicating as much.

Aside from these two changes, there are a handful of smaller changes that we
made by hand to keep the implementations of Reducer and OxideTC simpler,
though the need for these could be obviated with more work. Our implementation
does not support method call syntax, and so we translate method definitions
(which take `self`, `&self`, or `&mut self` as their first argument) into ordinary
function definitions with a named first argument at the method receiver's type.
Relatedly, some of the tests used traits in a trivial way to define methods
polymorphic in their receiver type. Much as with other methods, we translated
these into ordinary function definitions and used a polymorphic type for the receiver.
Further, rustc allows for a number of convenient programming patterns (like borrowing
from a constant, e.g. `&0`) which are not supported by our implementation. To deal with
these cases, we manually introduced temporaries (a process that rustc does
automatically). As a simplification for the type checker, OxideTC only reports the first
error that occurs in the program. To ensure that we find a correspondence between all
errors, we split up test files with multiple errors into one file per test.

Finally, an earlier version of our implementation required type annotations on
all let bindings, and so currently the majority of tests include fully-annotated
types. We later came to the realization that our typing judgment is very-nearly
a type _synthesis_ judgment as in bidirectional typechecking, and so the
implementation now supports unannotated let bindings by giving the name the type
synthesized from the expression being bound. This works for all expressions
except `abort!` which can produce any type and thus requires an
annotation. Further, if the programmer wishes to give the binding a broader type
via subtyping, they must provide it with an annotated type.

## Requirements

We require OCaml 4.08 for user-defined binding form support.

It requires `dune`.

The Rust to Oxide compiler is written in Rust and requires the Rust compiler and Cargo
(tested on 1.36.0).

## Running

The tests cases can be run using a test harness written in OCaml. Install the opam dependencies with:

```
opam install opam shexp stdio yojson utop ppx_deriving
```

And install the system dependency [jq](https://stedolan.github.io/jq/) (commandline json processor).

Then you can build it with:

```
dune build runner/runner.exe
```

And run it with:

```
dune exec runner/runner.exe
```

This will print out usage. To run a single test through the `reducer->oxide` pipeline, run:

```
dune exec runner/runner.exe check path/to/file.rs
```

To run over an entire directory, producing output `results.json` files in each subdirectory, run:

```
dune exec runner/runner.exe run path/
```

The meaning of the `results.json` file is:

```
{
  "matches": [ // tests that ran, and matched file.rs.output ],
  "doesntmatch": [ // tests that ran but did not match file.rs.output ],
  "missing": [ // tests that ran for which there is no file.rs.output ],
  "typeerror": [ // tests for which the oxide typechecker threw an error (most likely due to malformed syntax) ],
  "reducererror": [ // tests for which the reducer threw an error (most likely due to missing type annotations) ]
}
```

## Evaluation

You can run `eval.sh`, which will run the test harness on the `borrowck` test
suite, printing counts of the various categories above, as well as printing
counts for the various categories of excluded tests.
