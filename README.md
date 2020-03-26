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

## Running the Finite State Machine executable

### Setup dependencies

This library depends on `contrib`, `idris-ct` (`master` branch), `tparsec`, `optparse` and `typedefs-core` ([v0.1](https://github.com/typedefs/typedefs/tree/v0.1) release).

Install these libraries cloning them and then using `idris --install [ipkg filename].ipkg`.

### Build this library

Run

```
idris --build idris-stbx-core.ipkg
```

This will produce an executable file called `fficat`.

### Run the executable

You need to pass three arguments to the executable:

- `--tdef` requires a path to a file with Typedefs definitions
- `--fsm` requires a path to a file with a finite state machine definition
- `-f` requires a comma separated sequence of labels referring to the finite state machine transitions

For example, run

```
./fficat --TDefR tdefs.txt --fsm fsm.txt -f login,addProduct,addProduct,checkout
```

### Format of the Typedefs definitions

A sequence of [Typedefs](https://typedefs.com/) definitions, as provided for example in [tdefs.txt](./tdefs.txt)

### Format of finite state machine definition

This file contains the definition of a graph and is divided in two sections separated by a `---` line.

The first section contains a description of the vertices of the graph, one per line. A vertex is described by a `Nat` index and a string which refers to a `Typedef` defined in the file described in the section above.

The second section contains a description of the edges of the graph, one per line. A vertex is described by the index of the origin vertex, the index of the target vertex and a string which refers to an `Idris` function which should be defined in the code.

### Defining the functions used by the finite state machine

A complete and working example can be found at [`src/Computer/EcommerceExample.idr`](./src/Computer/EcommerceExample.idr).

It needs to include:

- imports of desired `C` functions.
- type definitions: definitions of the Typedefs needed to define the functions. ATTENTION: their definition needs to coincide exactly with the one given in the Typedefs definitions file.
- functions used in the finite state machine: if an edge is defined as `i j label` in the finite state machine specification, you need to have a function

```
label : Ty [] (unwrap TypeI) -> IO $ Ty [] (unwrap TypeJ)
```

where `TypeI` and `TypeJ` are the Typedefs associated to `i` and `j` respectively in the vertex section of the finite state machine definition.

- a conversion between edges and morphisms in the category `ioClosedTypedefsKleisliCategory FFI_C`, which is later used in `Main.idr` to execute the finite state machine.
