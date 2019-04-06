# Statebox Core

[![Build Status](https://travis-ci.com/statebox/idris-stbx-core.svg?branch=master)](https://travis-ci.com/statebox/idris-stbx-core)

This repository contains the core of the Statebox platform, comprising:

- open Petri nets
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

### Elba Build

Use

```
elba build
```

to build with [elba](https://github.com/elba/elba).

If you have authentication problems, run

```
eval `ssh-agent`
ssh-add
```

before running `elba`
