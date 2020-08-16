# ohso
[![Build Status](https://travis-ci.com/mgree/ohso.svg?branch=main)](https://travis-ci.com/mgree/mgt)

An implementation of the Hughes/Peyton Jones pretty printing library for Rust.

The code here follows
[pretty](https://hackage.haskell.org/package/pretty-1.1.3.6) package in Hackage.
NB that the original code is under a BSD 3-clause license (see
`LICENSE.original`) while _this_ package is under GPL 3 (see `LICENSE`).

# TODO

- [ ] Compare with [Haskell benchmarks](https://github.com/haskell/pretty/blob/master/bench/Bench.hs)
- [ ] Port [Haskell tests](https://github.com/haskell/pretty/tree/master/tests)
- [ ] Think about keeping annotations by reference
- [ ] Suite of examples (JSON, IMP, STLC)
- [ ] Profile and optimize `render` (e.g., `output` should be `rope` with good prepend operation; support using `Write` to avoid constructing the string)
- [ ] Figure out invariant around calls to `.reduce()` (every render involves a clone, per `render.rs` L221!)