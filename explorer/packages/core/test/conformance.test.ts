/**
 * Conformance: every TNF code emitted by the Lean enumerator must be a fixed point of the
 * TypeScript canonicalizer (canonicalize(code).code === code) and survive a parse/serialize
 * round-trip. This is what pins the TS port to the Lean ground truth — and the canonical code
 * is the database lookup key, so a divergence silently breaks paste-to-lookup.
 *
 * The fixture is committed (`test/fixtures/tnf-codes.txt`), generated from real
 * `lake exe beaver enumerate` output by `explorer/ingest gen-conformance`. It MUST be present,
 * non-empty, and cover the full BB(2,2)..BB(5,2) ladder — a missing/empty/width-incomplete
 * fixture fails the suite rather than passing trivially.
 */
import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { describe, expect, it } from "vitest";
import { canonicalize, parseMachine, serializeMachine } from "../src/index.js";

const fixture = join(dirname(fileURLToPath(import.meta.url)), "fixtures", "tnf-codes.txt");

function loadCodes(): string[] {
  if (!existsSync(fixture)) {
    throw new Error(
      `conformance fixture missing: ${fixture}. Regenerate with ` +
        `\`bb-ingest gen-conformance --file <export.tsv> --out test/fixtures/tnf-codes.txt\`.`,
    );
  }
  return readFileSync(fixture, "utf8")
    .split("\n")
    .map((l) => l.trim().split(/\s+/)[0] ?? "")
    .filter((l) => l.length > 0 && !l.startsWith("#"));
}

const codes = loadCodes();
const widths = new Set(codes.map((c) => c.split("_").length));

describe("Lean TNF conformance", () => {
  it("fixture is non-empty and covers the BB(2,2)..BB(5,2) ladder", () => {
    expect(codes.length).toBeGreaterThan(100);
    // Every size on the ladder must be represented — especially width 5, the largest and the
    // one with the most relabeling complexity. Without this, a 5-state divergence ships green.
    for (const w of [2, 3, 4, 5]) {
      expect(widths.has(w), `fixture is missing any width-${w} (BB(${w},2)) codes`).toBe(true);
    }
  });

  it("every code round-trips through parse/serialize", () => {
    for (const code of codes) {
      expect(serializeMachine(parseMachine(code))).toBe(code);
    }
  });

  it("every code is a fixed point of canonicalize", () => {
    // 5000 steps covers the enumeration's explore horizon (≤4100 for BB5) while staying fast.
    const offenders: string[] = [];
    for (const code of codes) {
      const out = canonicalize(parseMachine(code), { maxSteps: 5000 }).code;
      if (out !== code) offenders.push(`${code} -> ${out}`);
      if (offenders.length >= 20) break; // cap the report
    }
    expect(offenders).toEqual([]);
  });
});
