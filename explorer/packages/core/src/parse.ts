/**
 * Parse standard Busy Beaver machine codes into the {@link Machine} model.
 *
 * Mirrors Lean's `TM.Parse.pmachine`:
 *   - states separated by `_`
 *   - each state is a sequence of 3-char statements: `---` (halt) or `<digit><L|R><letter>`
 *   - the number of symbols is inferred from the first state and must be uniform
 *   - the number of states is the count of `_`-separated groups
 *   - write symbol and target label are reduced modulo the inferred sizes (as Lean does)
 */
import type { Dir, Machine, Stmt } from "./types.js";
import { letterState } from "./types.js";

export class ParseError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "ParseError";
  }
}

function parseStmt(chunk: string, nStates: number, nSymbols: number): Stmt {
  if (chunk === "---") return { kind: "halt" };
  const [w, d, l] = [chunk[0]!, chunk[1]!, chunk[2]!];
  if (!/[0-9]/.test(w)) throw new ParseError(`Expected a digit symbol, got '${w}' in '${chunk}'`);
  if (d !== "L" && d !== "R") throw new ParseError(`Expected L or R, got '${d}' in '${chunk}'`);
  if (!/[A-Z]/.test(l)) throw new ParseError(`Expected a state letter, got '${l}' in '${chunk}'`);
  // Lean reduces sym % (s+1) and lab % (l+1); replicate so out-of-range codes still parse.
  const write = Number(w) % nSymbols;
  const to = letterState(l) % nStates;
  return { kind: "next", write, dir: d as Dir, to };
}

function splitStmts(stateCode: string): string[] {
  if (stateCode.length === 0 || stateCode.length % 3 !== 0) {
    throw new ParseError(`State code '${stateCode}' length is not a positive multiple of 3`);
  }
  const out: string[] = [];
  for (let i = 0; i < stateCode.length; i += 3) out.push(stateCode.slice(i, i + 3));
  return out;
}

/**
 * Parse a machine code. Trims surrounding whitespace and ignores anything after
 * the first whitespace (codes are often followed by classification text).
 */
export function parseMachine(code: string): Machine {
  const token = code.trim().split(/\s+/)[0] ?? "";
  if (token.length === 0) throw new ParseError("Empty machine code");

  const stateCodes = token.split("_");
  if (stateCodes.length === 0) throw new ParseError("Empty machine code");

  const symbolCounts = stateCodes.map((s) => {
    if (s.length === 0 || s.length % 3 !== 0) {
      throw new ParseError(`State code '${s}' length is not a positive multiple of 3`);
    }
    return s.length / 3;
  });
  const nSymbols = symbolCounts[0]!;
  if (!symbolCounts.every((c) => c === nSymbols)) {
    throw new ParseError("All states must define the same number of symbols");
  }
  const nStates = stateCodes.length;

  const table: Stmt[][] = stateCodes.map((sc) =>
    splitStmts(sc).map((chunk) => parseStmt(chunk, nStates, nSymbols)),
  );

  return { nStates, nSymbols, table };
}

/** Like {@link parseMachine} but returns `null` instead of throwing. */
export function tryParseMachine(code: string): Machine | null {
  try {
    return parseMachine(code);
  } catch {
    return null;
  }
}
