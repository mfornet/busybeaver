/**
 * Core domain model for Busy Beaver Turing machines.
 *
 * This mirrors the Lean model in `Busybeaver/TM/Table.lean`:
 *   - A machine has `nStates` labels (Lean `l + 1`) and `nSymbols` symbols (Lean `s + 1`).
 *   - The transition table is label-major: `table[state][symbol]`.
 *   - State 0 is the start state `A`; symbol 0 is the blank symbol; the tape starts all-blank.
 *
 * Code format (identical to Lean's `Repr (Machine l s)` and `TM.Parse.pmachine`):
 *   states joined by `_`, each state = its per-symbol statements concatenated,
 *   a statement is `---` (halt) or `<write><L|R><stateLetter>`, e.g. `1RB1LC_1RC1RB`.
 */

export type Dir = "L" | "R";

/** A transition: either halt, or write a symbol, move, and go to a state. */
export type Stmt =
  | { kind: "halt" }
  | { kind: "next"; write: number; dir: Dir; to: number };

export const HALT: Stmt = { kind: "halt" };

export interface Machine {
  /** Number of states (Lean `l + 1`). */
  nStates: number;
  /** Number of symbols (Lean `s + 1`). */
  nSymbols: number;
  /** Label-major transition table: `table[state][symbol]`. */
  table: Stmt[][];
}

/** The canonical start configuration: state A (0), blank tape, head reading symbol 0. */
export const START_STATE = 0;
export const BLANK = 0;

export function next(write: number, dir: Dir, to: number): Stmt {
  return { kind: "next", write, dir, to };
}

/** State label as a letter: 0 -> "A", 1 -> "B", ... (matches Lean `Char.ofNat (l + 'A')`). */
export function stateLetter(state: number): string {
  return String.fromCharCode(65 + state);
}

/** Inverse of {@link stateLetter}: "A" -> 0. */
export function letterState(letter: string): number {
  return letter.charCodeAt(0) - 65;
}

/** Deep structural equality for machines (table contents). */
export function machineEquals(a: Machine, b: Machine): boolean {
  if (a.nStates !== b.nStates || a.nSymbols !== b.nSymbols) return false;
  for (let q = 0; q < a.nStates; q++) {
    for (let sym = 0; sym < a.nSymbols; sym++) {
      const x = a.table[q]![sym]!;
      const y = b.table[q]![sym]!;
      if (x.kind !== y.kind) return false;
      if (x.kind === "next" && y.kind === "next") {
        if (x.write !== y.write || x.dir !== y.dir || x.to !== y.to) return false;
      }
    }
  }
  return true;
}

/** Allocate an all-halt table of the given shape. */
export function emptyTable(nStates: number, nSymbols: number): Stmt[][] {
  return Array.from({ length: nStates }, () =>
    Array.from({ length: nSymbols }, () => ({ kind: "halt" }) as Stmt),
  );
}

/** Structural clone of a machine. */
export function cloneMachine(m: Machine): Machine {
  return {
    nStates: m.nStates,
    nSymbols: m.nSymbols,
    table: m.table.map((row) => row.map((s) => ({ ...s }))),
  };
}
