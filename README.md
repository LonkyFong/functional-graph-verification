Verified Functional Graph Algorithms using The Rocq Prover (Coq)
==============================================

This repository contains Rocq formalizations of
[algebraic graphs by Mohkov (2017)](https://doi.org/10.1145/3156695.3122956) and
[inductive graphs by Erwig (2001)](https://doi.org/10.1017/S0956796801004075).
The executable code was adopted mostly from the respective graph libraries
[Alga](https://github.com/snowleopard/alga) and
[FGL](https://github.com/haskell/fgl).

For more information, please read the associated thesis report, which in the future should be available on the University of Groningen website for people associated with the institution.

## Architecture
As a quick overview, codebase is comprised of four modules: utility, relational graphs, algebraic graphs, and inductive graphs.

[plantuml](https://plantuml.com/) diagrams are used to illustrate the architecture and dependencies for certain proofs, which are located in the `/documentation` folder, such that they can be kept up to date.
