# Statebox Core

This repository contains the core of the Statebox platform, comprising:

- open Petri nets
- wiring diagrams, which allow us to compose (glue) nets
- executions of Petri nets

The code is written in Idris, in terms of mathematical propositions and
proofs of category theoretic constructs.

The code is written using literate Idris, which allows us to integrate
documentation and code and export them both as an executable and as a human
readable document.

## Nix build

If you have Nix installed, you can do:

```
nix-build
```

For additional targets, have a look at the instructions in [default.nix](default.nix).

## Manual build

### Prerequisites

You'll need:

- [lhs2tex](https://github.com/kosmikus/lhs2tex/blob/master/INSTALL)
- [latexmk](https://mg.readthedocs.io/latexmk.html)
- [Idris](https://www.idris-lang.org/).

### Generate documentation

Use `make` to generate the PDF documentation. You will find it in the
`docs` directory.
Look directly in the [Makefile](Makefile) for additional options.

## File watcher

We use [SteelOverseer](https://github.com/schell/steeloverseer) to rebuild on
file changes.
If you modify any `.lidr` file, the whole package will be recompiled and the PDF
documentation will be updated.

To install SteelOverseer, first download and install the
[Stack](https://github.com/commercialhaskell/stack) build tool.

Then do:

```
stack install steeloverseer
```

Then, to launch the file watcher, just type:

```
sos
```
