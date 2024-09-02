# Lean Busy Beaver

This project contains an attempt at formalising results regarding Busy Beavers.

The objective is to merge deciders and their proof of correctness.

# Architecture of the project

The library/proofs are contained in [./Busybeaver/]:

- [./Busybeaver/Basic.lean] contains the base definition of Turing machines
- [./Busybeaver/Reachability.lean] contains many definitions related to reachability in TMs
- [./Busybeaver/ClosedSet.lean] defines a tool to prove non-halting based on [Closed Sets](https://wiki.bbchallenge.org/wiki/Closed_Set)
- [./Busybeaver/Deciders/] contains the code of deciders. They are designed as proof-carrying functions.

# Acknowledgment

I am heavily inspired by the following Coq formalisation of the problem: [busycoq](https://github.com/meithecatte/busycoq).