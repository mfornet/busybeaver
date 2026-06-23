/**
 * Turing machine simulation.
 *
 * Tape semantics match the Lean model: two-way-infinite tape filled with the blank
 * symbol (0), head starts at position 0 in state A (0). Direction `R` increments the
 * head position, `L` decrements it. A `halt` transition stops the machine; reaching a
 * state/symbol whose statement is `halt` is the only way to terminate.
 */
import type { Machine, Stmt } from "./types.js";
import { BLANK, START_STATE } from "./types.js";

/**
 * The transition out of `(state, sym)`, or `null` if the machine halts there (an explicit
 * `---` halt, or a cell with no statement). This is the single point where the transition
 * table is consulted, so `simulate` and `spaceTimeDiagram` step identically.
 */
function transition(
  machine: Machine,
  state: number,
  sym: number,
): Extract<Stmt, { kind: "next" }> | null {
  const stmt = machine.table[state]?.[sym];
  return stmt && stmt.kind === "next" ? stmt : null;
}

export type RunStatus = "halt" | "running";

export interface RunResult {
  status: RunStatus;
  /** Number of transitions executed. */
  steps: number;
  /** Final state and absolute head position. */
  state: number;
  head: number;
  /** Inclusive absolute bounds of cells visited. */
  leftmost: number;
  rightmost: number;
}

/**
 * A growable two-way tape. Non-negative positions live in `right` (index = pos),
 * negative positions in `left` (index = -pos - 1). Unwritten cells read as blank.
 */
class Tape {
  private right: number[] = [];
  private left: number[] = [];
  leftmost = 0;
  rightmost = 0;

  get(pos: number): number {
    const arr = pos >= 0 ? this.right : this.left;
    const idx = pos >= 0 ? pos : -pos - 1;
    return arr[idx] ?? BLANK;
  }

  set(pos: number, sym: number): void {
    if (pos >= 0) this.right[pos] = sym;
    else this.left[-pos - 1] = sym;
    if (pos < this.leftmost) this.leftmost = pos;
    if (pos > this.rightmost) this.rightmost = pos;
  }
}

/**
 * Run the machine until it halts or `maxSteps` transitions have been executed.
 * Returns `status: "running"` if the step budget is exhausted without halting.
 */
export function simulate(machine: Machine, maxSteps = 100_000): RunResult {
  const tape = new Tape();
  let state = START_STATE;
  let head = 0;
  let steps = 0;

  while (steps < maxSteps) {
    const stmt = transition(machine, state, tape.get(head));
    if (!stmt) {
      return {
        status: "halt",
        steps,
        state,
        head,
        leftmost: tape.leftmost,
        rightmost: tape.rightmost,
      };
    }
    tape.set(head, stmt.write);
    head += stmt.dir === "R" ? 1 : -1;
    state = stmt.to;
    steps++;
  }

  return {
    status: "running",
    steps,
    state,
    head,
    leftmost: tape.leftmost,
    rightmost: tape.rightmost,
  };
}

export interface SpaceTimeOptions {
  /** Maximum number of transitions to record (rows = recorded steps + 1). */
  maxSteps?: number;
}

/**
 * A compact space-time diagram suitable for rendering to a canvas.
 *
 * `symbols` is a row-major `height x width` grid of tape symbols, where row `t`
 * is the tape immediately *before* executing transition `t` (row 0 is the start
 * tape). Column `c` corresponds to absolute position `origin + c`.
 */
export interface SpaceTime {
  width: number;
  height: number;
  /** Absolute tape position of column 0. */
  origin: number;
  /** `height * width` tape symbols, row-major. */
  symbols: Uint8Array;
  /** Head column (relative to origin) for each row. */
  heads: Int32Array;
  /** Machine state for each row. */
  states: Uint8Array;
  halted: boolean;
  steps: number;
}

/**
 * Build a space-time diagram by simulating for up to `maxSteps` transitions.
 * Two-pass: simulate once to learn the visited window, then fill the grid.
 */
export function spaceTimeDiagram(machine: Machine, opts: SpaceTimeOptions = {}): SpaceTime {
  const maxSteps = opts.maxSteps ?? 1000;

  // Pass 1: discover bounds and total recorded steps. The head can finish one cell past
  // the written region (it moves after the final write, or halts on an unwritten cell), so
  // widen the window to include the final head position — otherwise its column is off-grid.
  const probe = simulate(machine, maxSteps);
  const recordedSteps = probe.steps;
  const origin = Math.min(probe.leftmost, probe.head);
  const right = Math.max(probe.rightmost, probe.head);
  const width = Math.max(1, right - origin + 1);
  const height = recordedSteps + 1;

  const symbols = new Uint8Array(height * width);
  const heads = new Int32Array(height);
  const states = new Uint8Array(height);

  // Pass 2: replay, snapshotting each row.
  const row = new Uint8Array(width);
  let state = START_STATE;
  let head = 0;
  let halted = false;

  for (let t = 0; t < height; t++) {
    symbols.set(row, t * width);
    heads[t] = head - origin;
    states[t] = state;
    const stmt = transition(machine, state, row[head - origin] ?? BLANK);
    if (t === height - 1) {
      halted = stmt === null;
      break;
    }
    if (!stmt) {
      halted = true;
      break;
    }
    row[head - origin] = stmt.write;
    head += stmt.dir === "R" ? 1 : -1;
    state = stmt.to;
  }

  return { width, height, origin, symbols, heads, states, halted, steps: recordedSteps };
}
