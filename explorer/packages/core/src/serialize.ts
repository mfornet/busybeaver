/**
 * Serialize a {@link Machine} back to standard code form.
 * This is the exact inverse of {@link parseMachine} and byte-identical to Lean's
 * `Repr (Machine l s)` (states joined by `_`, statements `---` or `<write><dir><letter>`).
 */
import type { Machine, Stmt } from "./types.js";
import { stateLetter } from "./types.js";

export function serializeStmt(s: Stmt): string {
  if (s.kind === "halt") return "---";
  return `${s.write}${s.dir}${stateLetter(s.to)}`;
}

export function serializeMachine(m: Machine): string {
  return m.table
    .map((row) => row.map(serializeStmt).join(""))
    .join("_");
}
