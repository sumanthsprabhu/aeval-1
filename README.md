About
=====

A functional synthesis tool based on the [Z3](https://github.com/Z3Prover/z3) SMT solver. It expects single-invocation specifications over linear integer/real arithmetic, encoded as `forall-exists` formulas, and aims at generating witnessing Skolem functions for (possibly, many) existentially-quantified variables. See the [VMCAI'19 paper](http://www.cs.fsu.edu/~grigory/aeval.pdf) for more details.

Installation
============

Compiles with gcc-7 (on Linux) and clang-900 (on Mac). Assumes preinstalled Gmp (with the `--enable-cxx` flag) and Boost 1.71 packages.

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (i.e., it needs a particular version of Z3 and installs it automatically)
* `make` to build AE-VAL

The binary of AE-VAL can be found in `build/tools/aeval/`.

Usage
==========

The tool takes as input formulas in SMT-LIB v2, e.g., the following specification for the `max` function:

`(assert (forall ((x1 Int) (x2 Int))`  
&nbsp;&nbsp;&nbsp;&nbsp;`(exists ((y Int)) `  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`(and (>= y x1) (>= y x2) (or (= y x1) (= y x2))))))`  

Running `aeval --skol max.smt2`  yields the realizability result `valid` and the extracted Skolem for the `y` variable:

`Iter: 2; Result: valid`  
`(define-fun y ((x1 Int)(x2 Int)) Int`  
&nbsp;&nbsp;&nbsp;&nbsp;`(ite (<= (+ x1 (- x2)) 0) x2 x1))`  
