import { describe, expect, it } from "vitest";
import { parseMachine, serializeMachine, ParseError, tryParseMachine } from "../src/index.js";

describe("parse / serialize", () => {
  const codes = [
    "1RB1LB_1LA---", // BB(2,2) champion (halt on B,1)
    "1RB---_1LB0RC_1LC1LA", // 3-state example
    "1RB0RB_1LA1RZ".replace("Z", "A"), // arbitrary 2x2
    "1RB1RC_1LC1RB_1RD0LE_1LA1LD_---0LB", // BB(5,2)-shape (Marxen-Buntrock-ish)
  ];

  it("round-trips code -> machine -> code", () => {
    for (const code of codes) {
      const m = parseMachine(code);
      expect(serializeMachine(m)).toBe(code);
    }
  });

  it("infers shape", () => {
    const m = parseMachine("1RB1LB_1LA---");
    expect(m.nStates).toBe(2);
    expect(m.nSymbols).toBe(2);
    expect(m.table[1]![1]).toEqual({ kind: "halt" });
    expect(m.table[0]![0]).toEqual({ kind: "next", write: 1, dir: "R", to: 1 });
  });

  it("ignores trailing classification text", () => {
    const m = parseMachine("1RB1LB_1LA---   halts by Cycler 7");
    expect(serializeMachine(m)).toBe("1RB1LB_1LA---");
  });

  it("rejects malformed codes", () => {
    expect(() => parseMachine("")).toThrow(ParseError);
    expect(() => parseMachine("1RB_1LA---")).toThrow(ParseError); // ragged symbol counts
    expect(() => parseMachine("1XB1LB_1LA---")).toThrow(ParseError); // bad direction
    expect(tryParseMachine("nonsense!!")).toBeNull();
  });

  it("supports >2 symbols", () => {
    const code = "1RB2LB1RZ".replace("Z", "A") + "_0LA2RB1LB"; // 2 states, 3 symbols
    const m = parseMachine(code);
    expect(m.nStates).toBe(2);
    expect(m.nSymbols).toBe(3);
    expect(serializeMachine(m)).toBe(code);
  });
});
