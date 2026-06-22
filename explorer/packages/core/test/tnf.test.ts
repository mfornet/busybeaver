import { describe, expect, it } from "vitest";
import {
  canonicalize,
  isInTNF,
  parseMachine,
  reflect,
  serializeMachine,
} from "../src/index.js";

describe("reflect", () => {
  it("is involutive and flips directions", () => {
    const m = parseMachine("1RB1LB_1LA---");
    const r = reflect(m);
    expect(serializeMachine(r)).toBe("1LB1RB_1RA---");
    expect(serializeMachine(reflect(r))).toBe("1RB1LB_1LA---");
  });
});

describe("canonicalize", () => {
  it("is identity on a machine already in TNF", () => {
    const code = "1RB1LB_1LA---";
    const res = canonicalize(parseMachine(code));
    expect(res.code).toBe(code);
    expect(res.inputInTNF).toBe(true);
    expect(res.reflected).toBe(false);
    expect(res.reachableStates).toBe(2);
    expect(res.reachableSymbols).toBe(2);
  });

  it("relabels states by order of first reference", () => {
    // A targets C before B exists; B is unreachable. Canonical renames C -> B.
    const input = "1RC---_------_1LA---";
    const res = canonicalize(parseMachine(input));
    expect(res.code).toBe("1RB---_1LA---_------");
    expect(res.inputInTNF).toBe(false);
    expect(res.reachableStates).toBe(2);
  });

  it("reflects when the first move is left", () => {
    // First executed transition (A,0) moves left -> reflect to make it move right.
    const input = "1LB---_1RA---";
    const res = canonicalize(parseMachine(input));
    expect(res.reflected).toBe(true);
    // After reflection the first transition moves right.
    expect(res.code.startsWith("1RB")).toBe(true);
  });

  it("renumbers symbols by order of first write", () => {
    // 3-symbol machine (9-char state codes) that writes symbol 2 before symbol 1.
    // A,0 -> 2RB ; B,0 -> 1LA ; rest halt.
    const input = "2RB------_1LA------";
    const res = canonicalize(parseMachine(input));
    // Symbol 2 is introduced first -> becomes canonical symbol 1; old 1 -> canonical 2.
    expect(res.code).toBe("1RB------_2LA------");
    expect(res.reachableSymbols).toBe(3);
  });

  it("is idempotent", () => {
    for (const code of ["1RC---_------_1LA---", "1LB---_1RA---", "2RB------_1LA------"]) {
      const once = canonicalize(parseMachine(code)).code;
      const twice = canonicalize(parseMachine(once)).code;
      expect(twice).toBe(once);
      expect(isInTNF(parseMachine(once))).toBe(true);
    }
  });
});
