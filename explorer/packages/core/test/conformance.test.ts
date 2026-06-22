/**
 * Conformance: every TNF code emitted by the Lean enumerator must be a fixed point of the
 * TypeScript canonicalizer (canonicalize(code).code === code) and survive a parse/serialize
 * round-trip. This is what pins the TS port to the Lean ground truth.
 *
 * In CI, `explorer/ingest/gen_conformance.py` (run via `lake exe beaver`) writes real codes
 * to `test/fixtures/tnf-codes.txt`. Locally, when that file is absent, we fall back to a small
 * set of hand-verified TNF codes so the suite always runs.
 */
import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { describe, expect, it } from "vitest";
import { canonicalize, parseMachine, serializeMachine } from "../src/index.js";

const here = dirname(fileURLToPath(import.meta.url));
const fixture = join(here, "fixtures", "tnf-codes.txt");

// Hand-traced TNF fixed points. Real BB(3..5) conformance comes from the Lean-generated
// fixture (`explorer/ingest/gen_conformance.py`) loaded in CI; this fallback is a smoke check.
const FALLBACK = [
  "1RB1LB_1LA---", // BB(2,2) champion
  "1RB0RB_1LB1LA", // small 2-state non-halter
];

function loadCodes(): { source: string; codes: string[] } {
  if (existsSync(fixture)) {
    const codes = readFileSync(fixture, "utf8")
      .split("\n")
      .map((l) => l.trim().split(/\s+/)[0] ?? "")
      .filter((l) => l.length > 0 && !l.startsWith("#"));
    if (codes.length > 0) return { source: `fixture (${codes.length} codes)`, codes };
  }
  return { source: "fallback (hand-verified)", codes: FALLBACK };
}

describe("Lean TNF conformance", () => {
  const { source, codes } = loadCodes();
  it(`source: ${source}`, () => {
    expect(codes.length).toBeGreaterThan(0);
  });

  it("every code round-trips through parse/serialize", () => {
    for (const code of codes) {
      expect(serializeMachine(parseMachine(code))).toBe(code);
    }
  });

  it("every code is a fixed point of canonicalize", () => {
    // 5000 steps covers the enumeration's explore horizon (≤4100 for BB5) while staying fast
    // across the full fixture.
    const offenders: string[] = [];
    for (const code of codes) {
      const out = canonicalize(parseMachine(code), { maxSteps: 5000 }).code;
      if (out !== code) offenders.push(`${code} -> ${out}`);
      if (offenders.length >= 20) break; // cap the report
    }
    expect(offenders).toEqual([]);
  });
});
