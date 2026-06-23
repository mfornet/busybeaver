/**
 * Tree Normal Form (TNF) canonicalization.
 *
 * The Lean enumerator (`Busybeaver/Enumerate/`) builds machines by filling the first
 * halting transition reached during simulation, introducing new states and symbols in
 * *min-unused* order. Equivalently, a machine is in TNF when:
 *
 *   1. Its first executed transition (state A reading blank) moves **right** — the
 *      enumeration seeds are `0RB…`/`1RB…` and left/right is reduced by reflection.
 *   2. States are numbered in the order they are first *targeted* during the run.
 *   3. Non-blank symbols are numbered in the order they are first *written*.
 *   4. Transitions on cells never reached from the start are `halt` (`---`).
 *
 * `canonicalize` maps an arbitrary machine to this representative. It is the same string
 * the Lean enumerator stores, so the result is a valid database lookup key. The
 * conformance test pins this to a sample of Lean-generated codes.
 */
import type { Dir, Machine, Stmt } from "./types.js";
import { BLANK, START_STATE, cloneMachine, emptyTable } from "./types.js";
import { serializeMachine } from "./serialize.js";

const flipDir = (d: Dir): Dir => (d === "L" ? "R" : "L");

/** Mirror image: swap every transition's direction. Preserves halting (tape reflected). */
export function reflect(m: Machine): Machine {
  const out = cloneMachine(m);
  for (const row of out.table) {
    for (let i = 0; i < row.length; i++) {
      const s = row[i]!;
      if (s.kind === "next") row[i] = { ...s, dir: flipDir(s.dir) };
    }
  }
  return out;
}

export interface CanonResult {
  /** The canonical machine. */
  machine: Machine;
  /** Its serialized code (the database key). */
  code: string;
  /** Whether a left/right reflection was applied to fix the first move to the right. */
  reflected: boolean;
  /** Whether the input was already exactly in TNF (`code === serialize(input)`). */
  inputInTNF: boolean;
  /** Count of states reachable from the start (introduced during the run). */
  reachableStates: number;
  /** Count of symbols that appear (introduced during the run), including the blank. */
  reachableSymbols: number;
  /** Transitions executed during canonicalization (capped by `maxSteps`). */
  steps: number;
  /** True if the run halted within the step budget while discovering reachable cells. */
  halted: boolean;
}

/**
 * Step budget for canonicalizing pasted machines on an interactive (render/submit) path.
 *
 * Enumerated leaves reach every non-halt cell within the decider's explore horizon (≤ a few
 * thousand steps for the BB(2,2)..BB(5,2) ladder), so this is comfortably sufficient to compute
 * the correct DB lookup key, while still bounding a pathological non-halting paste so it can't
 * spin for the full default budget. Centralized here so the UI call sites stay in sync.
 */
export const INTERACTIVE_CANON_STEPS = 10_000;

export interface CanonOptions {
  /**
   * Step budget for discovering reachable cells (default 100,000). Enumerated leaves reach
   * every non-halt cell within the decider's explore bound (≤ a few thousand steps), so this
   * is comfortably sufficient for any machine in the database; it only bounds the rare
   * non-halting input that never visits all of its cells.
   */
  maxSteps?: number;
}

/**
 * Compute the TNF representative of `m`.
 *
 * Best-effort for arbitrary input: introduction order is discovered by simulating from
 * the start. Unreached cells become `halt`, matching enumeration leaves.
 */
export function canonicalize(m: Machine, opts: CanonOptions = {}): CanonResult {
  const maxSteps = opts.maxSteps ?? 100_000;
  const totalCells = m.nStates * m.nSymbols;

  // (1) Fix the first move to the right. The first executed transition is table[A][blank].
  const first = m.table[START_STATE]?.[BLANK];
  const reflected = first?.kind === "next" && first.dir === "L";
  const work = reflected ? reflect(m) : m;

  // (2,3) Discover introduction order by simulating from the start.
  const stateMap = new Map<number, number>([[START_STATE, 0]]);
  const symMap = new Map<number, number>([[BLANK, 0]]);
  let nextState = 1;
  let nextSym = 1;

  // Record canonical statements per reached cell, keyed `state*nSymbols + symbol`.
  const reached = new Map<number, Stmt>();

  // Sparse tape: only non-blank cells stored.
  const tape = new Map<number, number>();
  let state = START_STATE;
  let head = 0;
  let steps = 0;
  let halted = false;

  while (steps < maxSteps) {
    const sym = tape.get(head) ?? BLANK;
    const stmt = work.table[state]?.[sym];
    if (!stmt || stmt.kind === "halt") {
      halted = true;
      break;
    }
    const cellKey = state * m.nSymbols + sym;
    if (!reached.has(cellKey)) {
      // First execution of this cell: introduce its written symbol and target state.
      if (!symMap.has(stmt.write)) symMap.set(stmt.write, nextSym++);
      if (!stateMap.has(stmt.to)) stateMap.set(stmt.to, nextState++);
      reached.set(cellKey, stmt);
    }
    // Execute.
    if (stmt.write === BLANK) tape.delete(head);
    else tape.set(head, stmt.write);
    head += stmt.dir === "R" ? 1 : -1;
    state = stmt.to;
    steps++;
    if (reached.size === totalCells) {
      // Every cell has been executed at least once; nothing new can be introduced.
      break;
    }
  }

  // Number of states/symbols actually introduced (reachable) before padding.
  const reachableStates = nextState;
  const reachableSymbols = nextSym;

  // Note: nStates/nSymbols are deliberately preserved (not trimmed to the reachable count).
  // The enumerator emits leaves with fully-unreachable trailing states as all-halt groups
  // (e.g. BB(3,2) `0RB---_0LA---_------`), so an N-state machine that only reaches k<N states
  // is a *distinct* TNF leaf in the N-state size class — its N-group code is the correct DB
  // key. Trimming would wrongly redirect it to a different machine in a smaller size class.

  // Assign the remaining (unreached) states/symbols arbitrary canonical labels so the
  // maps are total bijections. Their rows/columns are all halt and so do not affect code.
  for (let q = 0; q < m.nStates; q++) if (!stateMap.has(q)) stateMap.set(q, nextState++);
  for (let a = 0; a < m.nSymbols; a++) if (!symMap.has(a)) symMap.set(a, nextSym++);

  // (4) Build the canonical table: halt everywhere, then place relabeled reached cells.
  const table = emptyTable(m.nStates, m.nSymbols);
  for (const [cellKey, stmt] of reached) {
    if (stmt.kind !== "next") continue;
    const q = Math.floor(cellKey / m.nSymbols);
    const a = cellKey % m.nSymbols;
    table[stateMap.get(q)!]![symMap.get(a)!] = {
      kind: "next",
      write: symMap.get(stmt.write)!,
      dir: stmt.dir,
      to: stateMap.get(stmt.to)!,
    };
  }

  const machine: Machine = { nStates: m.nStates, nSymbols: m.nSymbols, table };
  const code = serializeMachine(machine);
  return {
    machine,
    code,
    reflected,
    inputInTNF: code === serializeMachine(m),
    reachableStates,
    reachableSymbols,
    steps,
    halted,
  };
}

/** Whether `m` is already exactly in TNF. */
export function isInTNF(m: Machine, opts: CanonOptions = {}): boolean {
  return canonicalize(m, opts).inputInTNF;
}
