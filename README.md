# Lean Busy Beaver

This project contains an attempt at formalising results regarding Busy Beavers.

The objective is to merge deciders and their proof of correctness.

More broadly, the project should rely as little as possible on
specific numbers of states and symbols. The idea is to have an
executable that allows querying and computing busy beaver values, as
well as a playground to play with TMs.

# Architecture of the project

The library/proofs are contained in [Busybeaver](./Busybeaver/):

- [Basic.lean](./Busybeaver/Basic.lean) contains the base definition of Turing machines
- [Reachability.lean](./Busybeaver/Reachability.lean) contains many definitions related to reachability in TMs
- [Problem.lean](./Busybeaver/Problem.lean) contains the definition of the busy beaver problem
- [ClosedSet.lean](./Busybeaver/ClosedSet.lean) defines a tool to prove non-halting based on [Closed Sets](https://wiki.bbchallenge.org/wiki/Closed_Set). It also provides the very convenient `closed_set` tactic, to call within the proofs.
- [Partial.lean](./Busybeaver/Partial.lean) defines TMs steps on finite tapes.
- [Enumerate](./Busybeaver/Enumerate/) contains everything related to
  justify the machine enumeration algorithm, and especially
  [Alg.lean](./Busybeaver/Enumerate/Alg.lean) contains a
  [TNF](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form)
  enumeration algorithm along with formal proofs.
- [Deciders](./Busybeaver/Deciders/) contains the code of deciders.
  They are designed as proof-carrying functions. Currently we have:
  [cyclers](./Busybeaver/Deciders/Cyclers.lean) and [translated
  cyclers](./Busybeaver/Deciders/TranslatedCyclers.lean).

# TODOs

You can find the ongoing tasks and goals [here](https://todo.sr.ht/~vigoux/busybeaver).

# Acknowledgment

I am heavily inspired by the following Coq formalisation of the problem: [busycoq](https://github.com/meithecatte/busycoq).

# Contibuting

This project follows and email workflow, we recommend to [setup git to
send emails](https://git-send-email.io). To setup for this specific
repo, a `lake` script is provided:

```
lake script run gitconfig
```

For additional guidelines about how to contribute and send patches, we
recommend reading [aerc's contributing guidelines](https://git.sr.ht/~rjarry/aerc/tree/master/item/CONTRIBUTING.md).
