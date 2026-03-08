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

## Results proved

| Value | Result |
|-------|--------|
| S(5) — max steps of halting 5-state 2-symbol TM | **47,176,870** |
| Σ(5) — max symbols written | **4,098** |
| space(5) — max tape cells visited | **12,289** |
| S(2,4) — max steps, 2-state 4-symbol TM | **3,932,964** |

All results are proved in the Coq-BB5 repository. The primary focus of this
document is BB(5) = S(5) = 47,176,870.

---

## High-level proof strategy — Proof by Reflection

The proof is a **proof by reflection** in Coq: algorithms (TNF enumeration +
all deciders) are *implemented in Coq*, proved correct, and then *run inside
Coq's kernel* via `native_compute`. Their outputs, combined with 13 individual
sporadic machine proofs, yield the final theorem.

**Coq-BB5 size:** 27,274 lines, 638 lemmas (plus 10,553 lines / 319 lemmas
imported from busycoq for sporadic machine proofs).

**Sole axiom used:** `functional_extensionality_dep` from Coq's standard
library (functions are equal iff equal at every point — widely accepted and
consistent).

**Main theorem:** Coq Lemma `BB5_value` in `BB5_Statement.v` (121-line file,
readable without Coq expertise).

### Steps

1. **TNF enumeration** (paper §3): enumerate all 5-state 2-symbol Turing
   machines in Tree Normal Form, reducing the search space from ~16.7 trillion
   to **181,385,789** machines.
2. **Decider pipeline** (paper §4): pass each machine through a pipeline; prove
   each machine either halts or does not halt.
3. **Sporadic machines** (paper §5): 13 machines survive the pipeline and
   receive individual hand-crafted Coq proofs.
4. **Conclusion** (paper §6): the single champion (Marxen-Buntrock, 1989)
   reaches 47,176,870 steps; all others halt sooner or don't halt.

---

## Tree Normal Form (TNF) Enumeration

**Paper §3 | Coq: `TNF.v`, `BB5_TNF_Enumeration.v`, `BB5_TNF_Enumeration_Roots/`**

Machines are enumerated arborescently. The TNF root has no transitions defined.
When a machine halts by reaching an *undefined transition*, every possible way to
fill that transition spawns a new subtree. Machines proved non-halting are
leaves. TNF eliminates machines with unreachable transitions and
state/symbol permutations.

**TNF reduction:** ~16.7 trillion → **181,385,789** enumerated machines (~91,958×
reduction).

The Coq proof parallelises compilation by splitting the TNF tree into 12
independent subtree files in `BB5_TNF_Enumeration_Roots/`, reducing compile
time from ~3 hours to ~45 minutes on 13 cores.

**Note:** this implementation enumerates machines starting with both `0` and `1`
as the first written symbol (unlike bbchallenge's TNF-1RB), making the search
space slightly larger but the proof simpler.

---

## CTL Framework

**Paper §4.2**

Almost all deciders use the **Closed Tape Language (CTL)** framework (Marxen and
Buntrock, first documented by Ligocki): find a set C of tape configurations that:

1. Contains the initial all-zero configuration.
2. Is closed under TM transitions (one step from any configuration in C stays in C).
3. Contains no halting configuration.

If such C exists, the machine cannot halt. Deciders differ in how they
*represent* and *compute* C.

---

## Decider Pipeline

**Paper §4 | Coq: `BB5_Deciders_Pipeline.v`, `BB5_Deciders_Generic.v`**

Deciders are applied in order. Each is proved correct in Coq.

### Summary table

| Decider | Nonhalt | Halt | Total | Paper | Coq theorem |
|---------|--------:|-----:|------:|-------|-------------|
| **Loops** | 126,994,099 | 48,379,711 | 175,373,810 | §4.3 | `loop1_decider_WF` (Thm 4.5) |
| **n-gram CPS** | 6,005,142 | — | 6,005,142 | §4.4 | `NGramCPS_decider_spec` (Thm 4.6) |
| **RepWL** | 6,577 | — | 6,577 | §4.5 | `RepWL_ES_decider_spec` (Thm 4.8) |
| **Halt Max** | — | 183 | 183 | §4, §6 | `halt_verifier` |
| **FAR** (verifier) | 23 | — | 23 | §4.6 | `dfa_nfa_verifier_spec` (Thm 4.9) |
| **WFAR** (verifier) | 17 | — | 17 | §4.7 | `MITM_WDFA_verifier_spec` (Thm 4.10) |
| **Sporadic Machines** | 13 | — | 13 | §5 | (individual) |
| **1RB-reduction** | 24 | — | 24 | §4.2 | `TM_to_NF_spec` |
| **Total** | **133,005,895** | **48,379,894** | **181,385,789** | | |

---

## Deciders — Details

### 1. Loops (`Decider_Loop.v`)

**Paper §4.3 | Theorem 4.5 = Coq `loop1_decider_WF`**

Detects two kinds of non-halting (together called "loops"):

- **Cycler:** machine re-enters the exact same `(state, tape)` configuration.
- **Translated Cycler:** same configuration but shifted in space (like a glider).

**Algorithm (`loop1_decider`):** Run for L steps. Scan the *transcript* — the
sequence of `(state, read-symbol, head-position)` triples — for a sub-transcript
of length l that appears twice consecutively. Head-position delta distinguishes
Cyclers (delta = 0) from Translated Cyclers (delta ≠ 0). This avoids storing
full tape content.

**Runs in pipeline:** L=130 (cheap, bulk), L=4100 (stragglers), L=1,050,000
(two final machines).

**Decides ~96.7% of all machines.** Of the ~127M nonhalting: ~86% Translated
Cyclers, ~14% Cyclers.

**Limitation:** Skelet #1 is technically a Translated Cycler with pre-period
~5.42×10^51 and period ~8.47 billion steps — no feasible L exists.

---

### 2. n-gram Closed Position Set (n-gram CPS) (`Decider_NGramCPS.v`)

**Paper §4.4 | Theorem 4.6 = Coq `NGramCPS_decider_spec`**

Represents configurations as *local snapshots*: the n symbols left of the head
(left n-gram), n symbols right (right n-gram), current state, and symbol under
the head. Builds a saturating set by forward-closing from the initial config. If
closed and halting not reachable → NONHALT.

**Three implementations** (increasingly powerful):

- **impl2** — standard binary alphabet, no history (faster). Used first.
- **impl1** — augments alphabet with a fixed-length *queue* of the last k
  `(state, symbol)` pairs seen at each cell.
- **LRU variant** — augments alphabet with an LRU-ordered set of `(state,
  symbol)` pairs per cell (up to 10 entries).

**Decides ~3.3% of machines** after loops.

External reference: [Nathan-Fenner/bb-simple-n-gram-cps](https://github.com/Nathan-Fenner/bb-simple-n-gram-cps)

---

### 3. Repeated Word List (RepWL) (`Decider_RepWL.v`)

**Paper §4.5 | Theorem 4.8 = Coq `RepWL_ES_decider_spec`**

Abstracts tape configurations as pairs of *regular expressions*:
`(block^k | block^{T+})` where each block is a fixed binary string of length l.
If a block repeats more than T times it is replaced by `block^{T+}` (unbounded
repetition). Macro-steps on these regex-configurations are simulated until the
graph closes or times out.

**Parameters per machine are hardcoded** (found by grid search in C++).
Block lengths l ∈ [1,38], repeat thresholds T ∈ {2,3,4}.

Parameters file: `BB5_Deciders_Hardcoded_Parameters/Decider_RepWL_Hardcoded_Parameters.v`

**Decides 6,577 machines** (all nonhalting).

---

### 4. Halt Max (`Decider_Halt_BB5.v`)

**Paper §4, §6 | Coq `halt_verifier`**

Simulates each machine for up to **47,176,870 steps**. If it halts within that
limit, it's confirmed as a halting machine.

Also used to confirm the *lower bound* BB(5) ≥ 47,176,870 by running the
champion machine (Marxen-Buntrock, 1989) and verifying it halts at exactly
that step count.

**Decides 183 halting machines** not caught by the cheap Loops decider.

---

### 5. Finite Automata Reduction (FAR) — Verifier (`Verifier_FAR.v`)

**Paper §4.6 | Theorem 4.9 = Coq `dfa_nfa_verifier_spec`**

A *co-CTL* approach: finds a regular language (NFA) containing all
*eventually-halting* configurations of the machine, but *not* the initial
all-zero config → machine doesn't halt.

Given a DFA certificate, constructs an NFA and verifies:
- Leading/trailing zeros are ignored.
- An "accepted steady state-set" certifies all halting configurations accepted.
- Matrix inequalities hold for each TM transition.
- Initial all-zero configuration is rejected.

**Only a verifier in Coq-BB5** — the DFA certificates for 23 machines are
hardcoded (found by weeks of brute-force DFA search). FAR is a *universal*
regular co-CTL method.

Certificates: `BB5_Deciders_Hardcoded_Parameters/Verifier_FAR_Hardcoded_Certificates.v`

**Decides 23 machines** (all nonhalting).

---

### 6. Weighted Finite Automata Reduction (WFAR) — Verifier (`Verifier_WFAR.v`)

**Paper §4.7 | Theorem 4.10 = Coq `MITM_WDFA_verifier_spec`**

Extension of FAR using *weighted* DFAs. Uses two deterministic WFAs (one
processes the tape left of head left-to-right, the other processes right of head
right-to-left). Configurations are encoded as `(left end-state, head state, head
symbol, right end-state, total weight)`. A closed accept set is computed using
Bellman-Ford to bound feasible weights.

WFAR goes **beyond regular CTL**: weighted automata can recognise non-regular
languages (e.g. 0^n 1^n). The 17 machines it solves are suspected to be
provably non-regular in the CTL sense.

**Only a verifier in Coq-BB5.** 17 hardcoded certificates — "Helices" machines
required hand-crafted certificates with ~50 states each.

Certificates: `BB5_Deciders_Hardcoded_Parameters/Verifier_WFAR_Hardcoded_Certificates.v`

External reference: [Iijil1/MITMWFAR](https://github.com/Iijil1/MITMWFAR)

**Decides 17 machines** (all nonhalting).

---

### 7. 1RB-reduction / NORMAL_FORM_TABLE_BASED

**Paper §4.2 | Coq `TM_to_NF_spec`, function `TM_to_NF`**

24 machines whose first transition is `0RB` are converted to an equivalent
machine with first transition `1RB` (simulate until first `1` is written, then
rename states). The `1RB` version is already in the hardcoded TABLE_BASED list.

**Decides 24 machines** (23 via FAR/WFAR certificates, 1 via Sporadic/Finned #3).

---

## Sporadic Machines

**Paper §5 | Coq: `BB5_Sporadic_Machines.v`, `BB5_Skelet17.v`, `BusyCoq/`**

After the full pipeline, **13 machines** remain. Each receives an individual,
hand-crafted non-halting proof. 12 of the 13 proofs are imported from the
[busycoq](https://github.com/meithecatte/busycoq) library (Maja Kądziołka);
the 13th (Skelet #17) is proved directly in Coq-BB5 by mxdys (~7,000 lines).

**Skelet #17 was the last machine solved, completing the proof of BB(5).**

### Three families

**Finned Machines** (5 machines: Finned #1–5)
Hold three unary numbers on tape with a linear invariant. Proofs use
hand-crafted certificates similar in flavor to WFAR. Coq: `BusyCoq/Finned{1-5}.v`.

**Shift Overflow Counters** (5 machines: Skelet #15, #26, #33, #34, #35)
Implement two independent binary counters. Halting would require a counter
overflow during a "Reset Phase" — the "Reset Invariant" shows this never
happens. Coq: `BusyCoq/Skelet{15,26,33,34,35}.v`.

**Three unique machines:**

| Machine | Description | Coq |
|---------|-------------|-----|
| Skelet #1 | Translated Cycler; pre-period ≥ 5.41×10^51 steps, period 8,468,569,863 | `BusyCoq/Skelet1.v` |
| Skelet #10 | Double Fibonacci Counter (Zeckendorf representation); desynchronisation never occurs | `BusyCoq/Skelet10.v` |
| Skelet #17 | Gray-code-like integer list; halts iff all entries zero/even (never happens); see [arXiv:2407.02426](https://arxiv.org/abs/2407.02426) | `BB5_Skelet17.v` |

---

## Navigating the Coq Submodule

```
Coq-BB5/
├── BusyCoq/                   # busycoq snapshot — 12 sporadic machine proofs
│   ├── Finned{1-5}.v
│   ├── Skelet{1,10,15,26,33,34,35}.v
│   └── ...
└── CoqBB5/
    ├── BB5/                   # main BB(5) proof
    │   ├── BB5_Statement.v                 # theorem statement (121 lines, readable)
    │   ├── BB5_Theorem.v                   # proof entry point
    │   ├── BB5_TNF_Enumeration.v           # gathers TNF tree results
    │   ├── BB5_TNF_Enumeration_Roots/      # parallelised subtrees (12 files)
    │   ├── BB5_Deciders_Pipeline.v         # pipeline definition + order
    │   ├── BB5_Deciders_Generic.v          # decider IDs + generic parameters
    │   ├── BB5_Sporadic_Machines.v         # collects 13 sporadic proofs
    │   ├── BB5_Skelet17.v                  # Skelet #17 (~7,000 lines)
    │   ├── BB5_Deciders_Hardcoded_Parameters/  # 8,032 hardcoded parameters
    │   │   ├── Decider_Halt_Hardcoded_Parameters.v
    │   │   ├── Decider_Loop_Hardcoded_Parameters.v
    │   │   ├── Decider_NGramCPS_Hardcoded_Parameters.v
    │   │   ├── Decider_RepWL_Hardcoded_Parameters.v
    │   │   ├── Verifier_FAR_Hardcoded_Certificates.v   # 23 FAR certs
    │   │   └── Verifier_WFAR_Hardcoded_Certificates.v  # 17 WFAR certs
    │   └── Deciders/                       # decider implementations
    │       ├── Decider_Loop.v
    │       ├── Decider_NGramCPS.v
    │       ├── Decider_RepWL.v
    │       ├── Decider_Halt_BB5.v
    │       ├── Verifier_FAR.v
    │       └── Verifier_WFAR.v
    ├── BB4/                   # BB(4) = 107
    ├── BB3/                   # BB(3) = 21
    ├── BB2/                   # BB(2) = 6
    ├── BB2x3/                 # BB(2,3) = 38
    └── BB2x4/                 # BB(2,4) = 3,932,964
```

## Navigating the PDF (`papers/2509.12337.pdf`)

| Section | Content |
|---------|---------|
| §1 | Introduction, background, statement of results |
| §2 | TNF enumeration algorithm |
| §3 | TNF enumeration — details |
| §4.2 | CTL framework overview; 1RB-reduction |
| §4.3 | Loops (Cyclers + Translated Cyclers) |
| §4.4 | n-gram CPS |
| §4.5 | RepWL |
| §4.6 | FAR |
| §4.7 | WFAR |
| §5 | Sporadic Machines — individual analyses |
| §6 | Results; main theorem; lower/upper bound |
| Appendix D | Exact pipeline parameters and counts |

---

## Relevance to This Lean Project

This Lean 4 project (`busybeaver`) aims to re-formalise these results with
proof-carrying deciders and verified enumeration. The Coq submodule and paper
are the primary references for:

- Which deciders to implement and in what order (see pipeline above).
- The correctness statement each decider must satisfy (see Coq theorem column).
- The TNF enumeration algorithm (`TNF.v`).
- The sporadic machine proofs (to eventually port or import).

**Current Lean deciders** (`Busybeaver/Deciders/`): Cyclers, Translated Cyclers
(= the Loops decider family from the Coq proof).
