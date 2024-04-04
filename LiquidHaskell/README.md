## Liquid Haskell
This folder contains the code for the case study Liquid Haskell

### Installing the tool

The installation of Liquid Haskell is straightforward, we need an SMT solver and we need to include liquid Haskell as a dependency to our project. Make sure to include the following GHC-option in your project: -fplugin=LiquidHaskell. For the SMT solver, we used Z3 since it is the most tested solver with Liquid Haskell. 
Other solvers that can be used are: CVC4  and MathSat . Installing the SMT solver is the hardest part, it can be quite a hassle to install it and to ensure the correct paths, yet a good installation guide should be sufficient to get it up and running quickly.

More information about installing liquid haskell can be found [here](https://ucsd-progsys.github.io/liquidhaskell/install/).