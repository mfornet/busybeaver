# BB(5) = 47,176,870 — Proof Overview

**Paper:** "Determination of the fifth Busy Beaver value"
**Authors:** The bbchallenge Collaboration (Blanchard, Briggs, Deka, Fenner, Forster,
Georgiev, House, Hunter, Iijil, Kądziołka, Kropitz, Ligocki, mxdys, Naściszewski,
savask, Stérin, Xu, Yuen, Zimmermann)
**arXiv:** [2509.12337](https://arxiv.org/abs/2509.12337) — stored locally at
`papers/2509.12337.pdf`
**Coq formalisation:** [ccz181078/Coq-BB5](https://github.com/ccz181078/Coq-BB5)
— available as a git submodule at `Coq-BB5/`

---

## High-level strategy

BB(5) means: the maximum number of steps a *halting* 5-state 2-symbol Turing
machine can take starting from an all-zero tape. The value is **47,176,870**,
achieved by the single champion machine.

The proof works by **exhaustive enumeration + decision**:

1. Enumerate all 5-state 2-symbol Turing machines in **Tree Normal Form (TNF)**.
2. For each machine, run a pipeline of deciders that proves it either *halts* or
   *does not halt*.
3. Among the halting machines, confirm the maximum step count is exactly
   47,176,870 (lower bound by running the champion; upper bound by deciding all
   others halt in fewer steps).

**Total machines enumerated:** 181,385,789

### Where to find this in the sources

- Paper: §2–§4 (enumeration and deciders)
- Coq: `Coq-BB5/CoqBB5/BB5/BB5_Statement.v` (statement),
  `BB5_Theorem.v` (entry point),
  `BB5_TNF_Enumeration.v` (enumeration),
  `BB5_Deciders_Pipeline.v` (pipeline)

---

## Tree Normal Form (TNF) Enumeration

Machines are enumerated in TNF to avoid redundancy. The enumeration builds a
*tree*: when a machine halts by meeting an *undefined transition*, every possible
way to fill that transition spawns a new subtree. Machines that are proved
non-halting are leaves.

The proof parallelises Coq compilation by splitting the tree into many
independent subtree files under `Coq-BB5/CoqBB5/BB5/BB5_TNF_Enumeration_Roots/`.

**Note:** this implementation enumerates machines that start by writing `0` *and*
`1`, making the search space slightly larger than some other implementations (like
bbchallenge's TNF-1RB) but yielding a simpler proof.

---

## Decider Pipeline

Deciders are applied in order. Each is proved correct in Coq: if it outputs
HALT/NONHALT then the machine actually halts/does not halt.

Pipeline defined in: `Coq-BB5/CoqBB5/BB5/BB5_Deciders_Pipeline.v`

### Summary table

| Decider | Nonhalt | Halt | Total | Coq file |
|---------|--------:|-----:|------:|----------|
| **Loops** | 126,994,099 | 48,379,711 | 175,373,810 | `Deciders/Decider_Loop.v` |
| **n-gram CPS** | 6,005,142 | — | 6,005,142 | `Deciders/Decider_NGramCPS.v` |
| **RepWL** | 6,577 | — | 6,577 | `Deciders/Decider_RepWL.v` |
| **Halt Max** | — | 183 | 183 | `Deciders/Decider_Halt_BB5.v` |
| **FAR** (verifier) | 23 | — | 23 | `Deciders/Verifier_FAR.v` |
| **WFAR** (verifier) | 17 | — | 17 | `Deciders/Verifier_WFAR.v` |
| **Sporadic Machines** | 13 | — | 13 | `BB5_Sporadic_Machines.v` |
| **1RB-reduction** | 24 | — | 24 | (pipeline logic) |
| **Total** | **133,005,895** | **48,379,894** | **181,385,789** | |

---

## Deciders — Details

### 1. Loops (`Decider_Loop.v`)

Detects two kinds of non-halting behaviour:

- **Case 2 (simple cycle):** the machine reaches the same `(state, tape)` pair
  twice.
- **Case 3 (translated cycle):** from configuration `…CBA(s,x)0…`, the machine
  reaches `…CB²A(s,x)0…` — i.e. the B block grows by one copy each macro-step.

Implementation: simulate for 2^k steps, check whether the `(state, input)` history
has a repeated suffix matching case 2 or 3.

Also used for halting detection (case 1) with `LOOP1_params_130` (fast, cheap)
and `LOOP1_params_4100` (more expensive, catches stragglers).

**Decides the vast majority** (~96.7%) of all enumerated machines.

Paper: §3.1 | Coq: `Deciders/Decider_Loop.v`

---

### 2. n-gram Closed Position Set (n-gram CPS) (`Decider_NGramCPS.v`)

Maintains finite sets L, R (n-gram sets for left/right tape context) and M (set
of `(state, 2n+1`-gram around head) that over-approximate all reachable
configurations. If the set is *closed* under one TM step and halting is not
reachable, the machine doesn't halt.

Two implementations:
- **impl2** — no update history (faster), used first in the pipeline.
- **impl1** — augments the alphabet with a fixed-size *queue* of the last k
  updates at each cell (slower but more powerful).
- **LRU variant** — uses an LRU cache instead of a fixed-size queue; used for
  the hardcoded-parameter machines.

**Decides ~3.3% of machines**, mostly after Loops.

Paper: §3.2 | Coq: `Deciders/Decider_NGramCPS.v`
External reference: [Nathan-Fenner/bb-simple-n-gram-cps](https://github.com/Nathan-Fenner/bb-simple-n-gram-cps)

---

### 3. Repeated Word List (RepWL) (`Decider_RepWL.v`)

A special case of CTL (Closed Tape Language) deciders. Abstracts tape
configurations as pairs of *regular expressions* of the form `(A₁A₂…Aₙ, state,
B₁B₂…Bₙ)` where each Aᵢ/Bᵢ is a block repeated some number of times (with a
"≥m" wildcard). Computes macro-steps on these abstractions and closes the set.

All 6,577 RepWL machines use **hardcoded parameters** (found by grid search in
external tools). Parameters are listed in:
`Coq-BB5/CoqBB5/BB5/BB5_Deciders_Hardcoded_Parameters/Decider_RepWL_Hardcoded_Parameters.v`

Paper: §3.3 | Coq: `Deciders/Decider_RepWL.v`

---

### 4. Halt Max (`Decider_Halt_BB5.v`)

Runs each machine for up to **47,176,870 steps**. If it halts, it's a halting
machine. Decides the 183 halting machines that weren't caught by the cheap Loops
decider.

Also used to establish the **lower bound** BB(5) ≥ 47,176,870 (by running the
champion machine and verifying it halts at exactly that step count).

Paper: §2.2 | Coq: `Deciders/Decider_Halt_BB5.v`, `Deciders/Verifier_Halt.v`

---

### 5. Finite Automata Reduction (FAR) — Verifier (`Verifier_FAR.v`)

Accepts a DFA as a certificate. Constructs an NFA that recognises all tape
configurations from which the machine *can* halt. Checks that the initial
all-zero tape is *not* accepted → machine doesn't halt.

**Does not search for the DFA** — DFAs for 23 machines are hardcoded as
certificates. Certificates: `BB5_Deciders_Hardcoded_Parameters/Verifier_FAR_Hardcoded_Certificates.v`

Paper: §3.4 | Coq: `Deciders/Verifier_FAR.v`

---

### 6. Weighted Finite Automata Reduction (WFAR) — Verifier (`Verifier_WFAR.v`)

Extension of FAR using *weighted* DFAs (two of them). Uses a RepWL-like
macro-step closure to find a closed set of configurations. Certificates for 17
machines are hardcoded.

Certificates: `BB5_Deciders_Hardcoded_Parameters/Verifier_WFAR_Hardcoded_Certificates.v`

Paper: §3.5 | Coq: `Deciders/Verifier_WFAR.v`
External reference: [Iijil1/MITMWFAR](https://github.com/Iijil1/MITMWFAR)

---

### 7. Hardcoded Parameters / TABLE_BASED

For 8,032 machines the decider *parameters* (or verifier *certificates*) are
explicitly provided rather than generated generically. Parameters were found by
grid search in external tools (mostly other programming languages).

Files in `Coq-BB5/CoqBB5/BB5/BB5_Deciders_Hardcoded_Parameters/`:
- `Decider_Halt_Hardcoded_Parameters.v` (183 halting machines)
- `Decider_Loop_Hardcoded_Parameters.v`
- `Decider_NGramCPS_Hardcoded_Parameters.v`
- `Decider_RepWL_Hardcoded_Parameters.v`
- `Verifier_FAR_Hardcoded_Certificates.v` (23 certificates)
- `Verifier_WFAR_Hardcoded_Certificates.v` (17 certificates)

---

### 8. 1RB-reduction / NORMAL_FORM_TABLE_BASED

24 machines whose first transition is `0RB` are converted to an equivalent
machine with first transition `1RB` (by simulating until the first `1` is written
and renaming states). The `1RB` version is then found in the TABLE_BASED list.

---

## Sporadic Machines

After the full pipeline, **13 machines** remain undecided. These are called
**5-state Sporadic Machines** and each receives an individual, hand-crafted
non-halting proof.

12 of the 13 proofs come from the [busycoq](https://github.com/meithecatte/busycoq)
library (by meithecatte), bundled in `Coq-BB5/BusyCoq/`. The 13th (Skelet #17)
is proved directly in `Coq-BB5/CoqBB5/BB5/BB5_Skelet17.v`.

Many are from Skelet's (Georgi Georgiev) 2003 bbfind holdout list:

| Machine | Behaviour |
|---------|-----------|
| Skelet #1 | Translated pattern; period 8,468,569,863 steps, appearing after ≥ 5.41×10⁵¹ steps |
| Skelet #10 | Double Fibonacci Counter |
| Skelet #17 | Connected to Gray code — proved in `BB5_Skelet17.v` (Gray-code structure, see [arXiv:2407.02426](https://arxiv.org/abs/2407.02426)) |
| Skelet #15, #26, #33, #34, #35 | Shift Overflow Counters |
| Finned #1–#5 | "Finned machines", originally claimed by Skelet; proofs in BusyCoq |

Coq files:
- `Coq-BB5/CoqBB5/BB5/BB5_Sporadic_Machines.v` — collects all proofs
- `Coq-BB5/BusyCoq/` — BusyCoq snapshot (12 proofs)
- `Coq-BB5/CoqBB5/BB5/BB5_Skelet17.v` — Skelet #17 proof

Paper: §4 (individual machine analyses)

---

## Navigating the Coq Submodule

```
Coq-BB5/
├── BusyCoq/               # busycoq snapshot — 12 sporadic machine proofs
└── CoqBB5/
    ├── BB5/               # main BB(5) proof
    │   ├── BB5_Statement.v            # theorem statement + TM definition
    │   ├── BB5_Theorem.v              # proof entry point
    │   ├── BB5_TNF_Enumeration.v      # gathers TNF tree results
    │   ├── BB5_TNF_Enumeration_Roots/ # parallelised subtrees
    │   ├── BB5_Deciders_Pipeline.v    # pipeline definition
    │   ├── BB5_Deciders_Generic.v     # decider IDs and generic parameters
    │   ├── BB5_Sporadic_Machines.v    # 13 sporadic machine proofs
    │   ├── BB5_Skelet17.v             # Skelet #17 individual proof
    │   ├── BB5_Deciders_Hardcoded_Parameters/   # 8032 hardcoded params
    │   └── Deciders/                  # decider implementations
    │       ├── Decider_Loop.v
    │       ├── Decider_NGramCPS.v
    │       ├── Decider_RepWL.v
    │       ├── Decider_Halt_BB5.v
    │       ├── Verifier_FAR.v
    │       └── Verifier_WFAR.v
    ├── BB4/               # BB(4) = 107 proof
    ├── BB3/               # BB(3) = 21 proof
    ├── BB2/               # BB(2) = 6 proof
    ├── BB2x3/             # BB(2,3) = 38 proof
    └── BB2x4/             # BB(2,4) = 3,932,964 proof
```

## Navigating the PDF

The paper (`papers/2509.12337.pdf`) is structured roughly as:

- **§1 Introduction** — background, statement of result, overview of proof
- **§2 Enumeration** — TNF enumeration, champion machine, lower/upper bound
- **§3 Deciders** — one subsection per decider (Loop, n-gram CPS, RepWL, FAR, WFAR)
- **§4 Sporadic Machines** — individual analyses of the 13 remaining machines
- **§5 Coq formalisation** — structure of Coq-BB5, axioms used, compilation

---

## Relevance to This Lean Project

This Lean project (`busybeaver`) aims to *re-formalise* these results in Lean 4
with proof-carrying deciders and verified enumeration. The Coq submodule and
paper serve as the primary reference for:

- Which deciders to implement (Cyclers/Loops, Translated Cyclers, n-gram CPS, …)
- The correctness statements each decider must satisfy
- The TNF enumeration algorithm
- The sporadic machine proofs (to eventually port or import)

Current Lean deciders (see `Busybeaver/Deciders/`): Cyclers, Translated Cyclers.
