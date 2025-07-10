Verified Functional Graph Algorithms using The Rocq Prover (Coq)
==============================================

This repository contains Rocq formalizations of
[algebraic graphs by Mohkov [2]](https://doi.org/10.1145/3156695.3122956) and
[inductive graphs by Erwig [1]](https://doi.org/10.1017/S0956796801004075).
The executable code was adopted mostly from the respective graph libraries
[Alga](https://github.com/snowleopard/alga) and
[FGL](https://github.com/haskell/fgl).

For more information, please read the associated thesis report, which in the future should be available on the University of Groningen website for people associated with the institution.


## Architecture
As a quick overview, codebase is comprised of five modules: utility, relational graphs, algebraic graphs, inductive graphs, and extraction.

[plantuml](https://plantuml.com/) diagrams are used to illustrate the architecture and dependencies for certain proofs, which are located in the `/documentation` folder, such that they can be kept up to date.


## Compilation
The project can be compiled by running:

```console
make
```

After updating the `_CoqProject` file run the command below to update the makefile.

```console
coq_makefile -f _CoqProject -o Makefile
```

The project uses Rocq version 8.18.0
and Haskell version 9.6.6 (for extracted code).


## References

[1] Martin Erwig. “Inductive graphs and functional graph algorithms”. In: *Journal of Functional Programming* 11.5 (2001), pp. 467–492. DOI: [10.1017/S0956796801004075](https://doi.org/10.1017/S0956796801004075).

[2] Andrey Mokhov. “Algebraic graphs with class (functional pearl)”. In: *SIGPLAN Not.* 52.10 (Sept. 2017), pp. 2–13. issn: 0362-1340. DOI: [10.1145/3156695.3122956](https://doi.org/10.1145/3156695.3122956).
