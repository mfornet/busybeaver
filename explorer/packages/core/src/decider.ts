/**
 * Decider attribution: a structured mirror of Lean's `DeciderConfig` (see `Main.lean`).
 *
 * The database stores, per decided machine, the exact decider + parameters that resolved
 * it. From that we render both a human label and a reproducible command:
 *
 *   lake exe beaver decide <code> --config <one-decider.json>
 *
 * whose `--config` payload is `[deciderToJson(decider)]`. Running it re-runs that single
 * decider in the project and shows it deciding the machine.
 */

export type Decider =
  | { kind: "translatedCycler"; n: number }
  | { kind: "cycler"; n: number }
  | { kind: "explore"; n: number }
  | { kind: "loop1"; n: number }
  | { kind: "backwardsReasoning"; n: number }
  | { kind: "nGramCPS"; n: number; bound: number }
  | { kind: "nGramCPSHistory"; history: number; left: number; right: number; bound: number }
  | { kind: "nGramCPSLRU"; left: number; right: number; bound: number }
  | { kind: "repWL"; len: number; threshold: number; maxT: number; bound: number }
  | { kind: "bb5TableExecutable" }
  | { kind: "bb5TableAll" };

export type DeciderJson =
  | { translatedCycler: number }
  | { cycler: number }
  | { explore: number }
  | { loop1: number }
  | { backwardsReasoning: number }
  | { nGramCPS: { n: number; bound: number } }
  | { nGramCPSHistory: { history: number; left: number; right: number; bound: number } }
  | { nGramCPSLRU: { left: number; right: number; bound: number } }
  | { repWL: { len: number; threshold: number; maxT: number; bound: number } }
  | "bb5TableExecutable"
  | "bb5TableAll";

/** Convert a decider to the JSON value Lean's `FromJson DeciderConfig` accepts. */
export function deciderToJson(d: Decider): DeciderJson {
  switch (d.kind) {
    case "translatedCycler": return { translatedCycler: d.n };
    case "cycler": return { cycler: d.n };
    case "explore": return { explore: d.n };
    case "loop1": return { loop1: d.n };
    case "backwardsReasoning": return { backwardsReasoning: d.n };
    case "nGramCPS": return { nGramCPS: { n: d.n, bound: d.bound } };
    case "nGramCPSHistory":
      return { nGramCPSHistory: { history: d.history, left: d.left, right: d.right, bound: d.bound } };
    case "nGramCPSLRU": return { nGramCPSLRU: { left: d.left, right: d.right, bound: d.bound } };
    case "repWL":
      return { repWL: { len: d.len, threshold: d.threshold, maxT: d.maxT, bound: d.bound } };
    case "bb5TableExecutable": return "bb5TableExecutable";
    case "bb5TableAll": return "bb5TableAll";
  }
}

/** Parse a Lean DeciderConfig JSON value back into a structured {@link Decider}. */
export function deciderFromJson(j: DeciderJson): Decider {
  if (j === "bb5TableExecutable") return { kind: "bb5TableExecutable" };
  if (j === "bb5TableAll") return { kind: "bb5TableAll" };
  if ("translatedCycler" in j) return { kind: "translatedCycler", n: j.translatedCycler };
  if ("cycler" in j) return { kind: "cycler", n: j.cycler };
  if ("explore" in j) return { kind: "explore", n: j.explore };
  if ("loop1" in j) return { kind: "loop1", n: j.loop1 };
  if ("backwardsReasoning" in j) return { kind: "backwardsReasoning", n: j.backwardsReasoning };
  if ("nGramCPS" in j) return { kind: "nGramCPS", ...j.nGramCPS };
  if ("nGramCPSHistory" in j) return { kind: "nGramCPSHistory", ...j.nGramCPSHistory };
  if ("nGramCPSLRU" in j) return { kind: "nGramCPSLRU", ...j.nGramCPSLRU };
  if ("repWL" in j) return { kind: "repWL", ...j.repWL };
  throw new Error(`unrecognized decider JSON: ${JSON.stringify(j)}`);
}

/** Human-readable label, matching Lean's `ToString DeciderConfig`. */
export function deciderLabel(d: Decider): string {
  switch (d.kind) {
    case "translatedCycler": return `Translated cycler ${d.n}`;
    case "cycler": return `Cycler ${d.n}`;
    case "explore": return `Explore ${d.n}`;
    case "loop1": return `Loop1 ${d.n}`;
    case "backwardsReasoning": return `Backwards Reasoning ${d.n}`;
    case "nGramCPS": return `NGram CPS n=${d.n} bound=${d.bound}`;
    case "nGramCPSHistory":
      return `NGram CPS history=${d.history} left=${d.left} right=${d.right} bound=${d.bound}`;
    case "nGramCPSLRU": return `NGram CPS LRU left=${d.left} right=${d.right} bound=${d.bound}`;
    case "repWL":
      return `RepWL len=${d.len} threshold=${d.threshold} maxT=${d.maxT} bound=${d.bound}`;
    case "bb5TableExecutable": return "BB5 executable hardcoded table";
    case "bb5TableAll": return "BB5 full hardcoded table";
  }
}

/** The single-decider config file payload that reproduces this decision. */
export function deciderConfigFile(d: Decider): string {
  return JSON.stringify([deciderToJson(d)], null, 2);
}

/** Top-level kind of a raw DeciderConfig JSON value (string variant, or the single object key). */
export function deciderKindFromJson(j: DeciderJson): string {
  if (typeof j === "string") return j;
  const keys = Object.keys(j);
  return keys[0] ?? "unknown";
}

/**
 * Resilient label for a raw DeciderConfig JSON. Falls back to the bare kind if the variant is
 * not one this build knows about — so a newly-added Lean decider degrades gracefully in the UI
 * instead of throwing. (`@bb/core` is a hand-port of Lean's derived `DeciderConfig`; new
 * variants must be added here, and `decider.test.ts` pins the known ones.)
 */
export function deciderLabelFromJson(j: DeciderJson): string {
  try {
    return deciderLabel(deciderFromJson(j));
  } catch {
    return deciderKindFromJson(j);
  }
}

/**
 * The reproducible single-decider config file, built directly from the raw JSON (passthrough),
 * so it works even for decider variants this build doesn't model structurally.
 */
export function deciderConfigFileFromJson(j: DeciderJson): string {
  return JSON.stringify([j], null, 2);
}

/**
 * The reproducible CLI command. `--config` points at `decider.json`, the file the UI shows
 * alongside it holding `[<the decider JSON>]`.
 */
export function decideCommand(code: string): string {
  return `lake exe beaver decide ${code} --config decider.json`;
}
