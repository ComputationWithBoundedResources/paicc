# paicc

Automated runtime analysis of *Integer Transition Systems* via *growth-rate analysis of Flowchart* programs.

## Requirements

This package depends on the [Tyrolean Complexity Tool](https://github.com/ComputationWithBoundedResources/tct-its/)
and the [LARE](https://github.com/ComputationWithBoundedResources/lare/) package.

Following executables are required in `$PATH`.
  * [yices](http://yices.csl.sri.com/) (tested with version 2.3)
  * [otimathsat](http://optimathsat.disi.unitn.it/) (tested with version 1.4.5)


## Installation

### Using Stack
We recommend using [stack](https://github.com/commercialhaskell/stack) with the accompanying `stack.yaml` file.
To build and install the package run following command:

```bash
stack build paicc
```

## Example Usage
The installation provides an executable `paicc-exe`.

```bash
$ cat nesting.its
(GOAL COMPLEXITY)
(STARTTERM (FUNCTIONSYMBOLS l0))
(VAR A B C D)
(RULES
  l0(A, B, C, D) -> l1(0, B, C, D)
  l1(A, B, C, D) -> l2(A, B, 0, 0)         :|: B > 0
  l2(A, B, C, D) -> l2(A, B, C + 1, D + C) :|: C < B
  l2(A, B, C, D) -> l1(A + D, B - 1, C, D) :|: C >= B
  l1(A, B, C, D) -> l3(A, B, C, D)         :|: B <= 0
  l3(A, B, C, D) -> l3(A - 1, B, C, D)     :|: A > 0
)
$ stack exec paicc-exe -- nesting.its
YES(?,POLY)
...
```

