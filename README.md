# What

Minimal example of using [lhs2tex](https://github.com/kosmikus/lhs2tex/blob/master/INSTALL) with [Idris](https://www.idris-lang.org/).

# Setup

You need `lhs2tex`, `latexmk` and `idris`.

# Usage

Run just make to extract the code and build the PDF, see `Makefile` for more information

# References

- [lhs2tex tutorial](http://ozark.hendrix.edu/~yorgey/490/static/lhs2TeX-tutorial.pdf)
- [lhs2tex guide](https://www.andres-loeh.de/lhs2tex/Guide2-1.17.pdf)
- [lhs2tex presentation](https://www.andres-loeh.de/lhs2TeX-IFIP.pdf)

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
