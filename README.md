# Statebox Core

This repository contains the core of the Statebox platform.

## Literate Idris

The code is written using Literate Idris, so that it is possible to integrate
documentation and code and export them both as an executable and as a human
readable document.

### Tools

You'll need

- [lhs2tex](https://github.com/kosmikus/lhs2tex/blob/master/INSTALL)
- [latexmk](https://mg.readthedocs.io/latexmk.html)
- [Idris](https://www.idris-lang.org/).

### Generate documentation

Go into the `latex Documentation` directory and use `make` to generate the Pdf
documentation.
Look directly in the [Makefile](Makefile) for additional options.

## Live Checks

We use [SteelOverseer](https://github.com/schell/steeloverseer) to react to
file changes and check the types on the whole projecct.

To install SteelOverseer, first download and install the
[Stack](https://github.com/commercialhaskell/stack) build tool.

Then do

```
stack install steeloverseer
```

Then, to launch the file watcher, just use

```
sos
```
