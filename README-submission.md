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
