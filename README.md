# Lean Busy Beaver

This project contains an attempt at formalising results regarding Busy Beavers.

The objective is to merge deciders and their proof of correctness.

# Architecture of the project

The library/proofs are contained in [Busybeaver](./Busybeaver/):

- [Basic.lean](./Busybeaver/Basic.lean) contains the base definition of Turing machines
- [Reachability.lean](./Busybeaver/Reachability.lean) contains many definitions related to reachability in TMs
- [Problem.lean](./Busybeaver/Problem.lean) contains the definition of the busy beaver problem as well as algorithms to compute it
- [ClosedSet.lean](./Busybeaver/ClosedSet.lean) defines a tool to prove non-halting based on [Closed Sets](https://wiki.bbchallenge.org/wiki/Closed_Set)
- [Enumerate](./Busybeaver/Enumerate/) contains everything related to
  justify the machine enumeration algorithm, and especially
  [Alg.lean](./Busybeaver/Enumerate/Alg.lean) contains a
  [TNF](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form)
  enumeration algorithm along with formal proofs.
- [Deciders](./Busybeaver/Deciders/) contains the code of deciders. They are designed as proof-carrying functions.

# Broad TODOs

The project attempts to reconstruct the proofs of busybeaver
computations. Here are a bunch of ongoing/todo work. They are sorted
in a random order, and agglomerated by broad categories:

- Formal-only work
    1. Setup definition used for shift-rules and [inductive proofs](https://wiki.bbchallenge.org/wiki/Inductive_Proof_System).
       A good short term goal can be to prove nontermination for the
       TM mentionned in the aforementionned page.
    2. Setup the definitions to reason about individual TMs
    3. Finish the proof of the TNF enumeration algorithm (NB: some
       lemmas may be wrong and need to tweaked to finish the proof)
- Implementation-only work
    1. Find a way to have more parallel evaluation when enumerating TMs
    2. Enhance logging of the main executable
    3. Accelerate BBResult merging: for now we use the tragically slow
       `Finset.union`, we could actually use `Finset.disjUnion` to
       reduce union to list concatenation.
- Mixed work
    1. More deciders !
    2. Write (and prove) a TNF-1RB enumeration algorithm
    3. Allow for caching on disk (seems tricky, might involve developing _certificates_ of non-termination) ?

# Acknowledgment

I am heavily inspired by the following Coq formalisation of the problem: [busycoq](https://github.com/meithecatte/busycoq).
