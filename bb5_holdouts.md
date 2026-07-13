# BB(5,2) holdout list — RESOLVED

> **Status (2026-07-13): all 4 holdouts are now decided (`loops`).** The NGramCPS
> over-approximation described under "Root cause" was fixed (see below); each machine
> now closes at its exact table-routed params and returns a genuine, axiom-clean
> `.loops_prf` non-halting proof. A full `beaver 5 2` re-run is expected to yield an
> empty holdout list.

Machines that *were* left `unknown` by the `bb5DefaultConfig` pipeline before the fix.

- **Generated:** 2026-07-10 from `main` @ `7809309`
- **Command:** `.lake/build/bin/beaver 5 2 --output bb5_holdouts.txt`
- **Run:** 181,385,786 TNF machines processed in 4h46m; confirms `BB(5,2) ≥ 47176870` (the known value).
- **Count:** 4 holdouts (plain codes in [bb5_holdouts.txt](bb5_holdouts.txt), directly usable with `beaver audit bb5_holdouts.txt`).

## The fix (2026-07-13)

Root cause 1 below was a localized over-approximation: on a step, our search recorded
the *shifted, head-adjacent* window (`newLeft`/`newRight`, offset 0, containing the
freshly-written symbol) into the n-gram set, whereas Coq records the *old* window
(`xset_ins ls l0` / `xset_ins rs r0`, `Decider_NGramCPS.v:296,309`). The offset-0
windows polluted the boundary-reconstruction pool and produced spurious halting edges.

Fixed by recording `cfg.left`/`cfg.right` (the old window) in `expandRight`/`expandLeft`
(`Deciders/NGramCPS/Basic.lean`, both the concrete and `Generic` versions), and
weakening the window invariant `AllLeftWindowsIn`/`AllRightWindowsIn` from "all offsets
`k ≥ 0`" to "offsets `k ≥ 1`" (the offset-0 window is carried by the matching
`PartialConfig`), which is exactly Coq's `xset_matches … n > 1`. Soundness is preserved
(proofs re-checked, axiom-clean: `propext, Classical.choice, Quot.sound`). The fix makes
the abstraction *strictly more precise*, so it cannot regress any previously-decided
machine.

Verified: each machine now returns `loops` at its table params — m1 (history=3, len=12),
m2/m3 (len=17), m4 (len=20).

## The 4 machines

All four are routed by the BB5 table (`Busybeaver/Deciders/BB5TableEntries.lean`, `nGramEntries`) to the **nGramCPS** decider, and our Lean nGramCPS port returned `unknown` at those params *before the fix*. None are sporadic / FAR / repWL machines — this was a single root cause.

| # | Machine code | Table routing | Table line |
|---|---|---|---|
| 1 | `1RB0LA_0RC---_1LC1RD_0RE1LA_1RA1RD` | `.nGram 3 12 5000001` (history=3, len=12) | BB5TableEntries.lean:1252 |
| 2 | `1RB0LA_0RC---_1RD0RD_1LE0RE_1RA0LC` | `.nGram 0 17 5000001` (impl2, len=17) | BB5TableEntries.lean:1627 |
| 3 | `1RB0LB_1LC0RE_1LD0RC_0LE---_1LA0LA` | `.nGram 0 17 5000001` (impl2, len=17) | BB5TableEntries.lean:1628 |
| 4 | `1RB0LD_1RC0LB_0RD---_1RE0RE_1LA0RA` | `.nGram 0 20 5000001` (impl2, len=20) | BB5TableEntries.lean:1630 |

## Root cause (historical — now fixed, see "The fix" above)

Our NGramCPS abstraction was coarser than Coq's at equal parameters. Coq's pipeline
decides these with nGram at the table params; ours did not. This was traced to the
window-recording over-approximation described in "The fix" above (option 1 below).

1. **[DONE]** Fix the over-approximation in the abstraction's boundary reconstruction
   (`expandLeft`/`expandRight`, `Deciders/NGramCPS/Basic.lean`) so it matches Coq's
   strength — these now close at the table params.
2. Add larger-window nGram passes to `bb5DefaultConfig` (the June fix used this to
   close 16 of the earlier 19; these 4 survived it). No longer needed for these 4.

`.nGram 0 N` = `nGramCPSDecider {n := N}` (plain CPS); `.nGram H N` with H>0 =
`nGramCPSHistoryDecider {history := H, left = right := N}`.
