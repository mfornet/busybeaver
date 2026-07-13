# BB(5,2) holdout list

Machines left `unknown` by the current `bb5DefaultConfig` pipeline.

- **Generated:** 2026-07-10 from `main` @ `7809309`
- **Command:** `.lake/build/bin/beaver 5 2 --output bb5_holdouts.txt`
- **Run:** 181,385,786 TNF machines processed in 4h46m; confirms `BB(5,2) ≥ 47176870` (the known value).
- **Count:** 4 holdouts (plain codes in [bb5_holdouts.txt](bb5_holdouts.txt), directly usable with `beaver audit bb5_holdouts.txt`).

## The 4 machines

All four are routed by the BB5 table (`Busybeaver/Deciders/BB5TableEntries.lean`, `nGramEntries`) to the **nGramCPS** decider, and our Lean nGramCPS port returns `unknown` at those params. None are sporadic / FAR / repWL machines — this is a single root cause.

| # | Machine code | Table routing | Table line |
|---|---|---|---|
| 1 | `1RB0LA_0RC---_1LC1RD_0RE1LA_1RA1RD` | `.nGram 3 12 5000001` (history=3, len=12) | BB5TableEntries.lean:1252 |
| 2 | `1RB0LA_0RC---_1RD0RD_1LE0RE_1RA0LC` | `.nGram 0 17 5000001` (impl2, len=17) | BB5TableEntries.lean:1627 |
| 3 | `1RB0LB_1LC0RE_1LD0RC_0LE---_1LA0LA` | `.nGram 0 17 5000001` (impl2, len=17) | BB5TableEntries.lean:1628 |
| 4 | `1RB0LD_1RC0LB_0RD---_1RE0RE_1LA0RA` | `.nGram 0 20 5000001` (impl2, len=20) | BB5TableEntries.lean:1630 |

## Root cause

Our NGramCPS abstraction is coarser than Coq's at equal parameters (see the
`bb5-undecided-holdouts-diagnosis` note). Coq's pipeline decides these with nGram
at the table params; ours does not. Likely fixes, in order of preference:

1. Fix the over-approximation in the abstraction's boundary reconstruction
   (`expandLeft`/`expandRight`/`matchingLastSymbols`, `Deciders/NGramCPS/Basic.lean`)
   so it matches Coq's strength — then these close at the table params.
2. Add larger-window nGram passes to `bb5DefaultConfig` (the June fix used this to
   close 16 of the earlier 19; these 4 survived it).

`.nGram 0 N` = `nGramCPSDecider {n := N}` (plain CPS); `.nGram H N` with H>0 =
`nGramCPSHistoryDecider {history := H, left = right := N}`.
