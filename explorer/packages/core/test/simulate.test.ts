import { describe, expect, it } from "vitest";
import { parseMachine, simulate, spaceTimeDiagram } from "../src/index.js";

describe("simulate", () => {
  it("BB(2,2) champion halts and writes four 1s", () => {
    const m = parseMachine("1RB1LB_1LA---");
    const r = simulate(m, 1000);
    expect(r.status).toBe("halt");
    // Five transitions are executed before the halting cell (B,1) is read.
    expect(r.steps).toBe(5);
    // Visited cells -2..1 inclusive, all four non-blank.
    expect(r.leftmost).toBe(-2);
    expect(r.rightmost).toBe(1);
  });

  it("reports running when the budget is exhausted", () => {
    // A simple right-moving non-halter: A,0 -> 1RB ; B,0 -> 1RA ; (1-cells never read)
    const m = parseMachine("1RB---_1RA---");
    const r = simulate(m, 50);
    expect(r.status).toBe("running");
    expect(r.steps).toBe(50);
  });

  it("space-time diagram has consistent shape", () => {
    const m = parseMachine("1RB1LB_1LA---");
    const st = spaceTimeDiagram(m, { maxSteps: 1000 });
    expect(st.halted).toBe(true);
    expect(st.height).toBe(st.steps + 1);
    expect(st.symbols.length).toBe(st.height * st.width);
    // Row 0 is the all-blank start tape.
    expect([...st.symbols.slice(0, st.width)].every((s) => s === 0)).toBe(true);
    // Head column for row 0 maps to absolute position 0.
    expect(st.heads[0]! + st.origin).toBe(0);
  });

  it("keeps every head column in-grid even when the head ends past the written region", () => {
    // '1RA---' marches right writing 1s; after the budget the head sits one cell past the
    // rightmost write. Every recorded head (including the last) must be within [0, width).
    const m = parseMachine("1RA---");
    const st = spaceTimeDiagram(m, { maxSteps: 3 });
    for (let t = 0; t < st.height; t++) {
      expect(st.heads[t]!, `row ${t} head off-grid`).toBeGreaterThanOrEqual(0);
      expect(st.heads[t]!).toBeLessThan(st.width);
    }
  });
});
