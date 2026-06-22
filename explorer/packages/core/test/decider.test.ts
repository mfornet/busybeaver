import { describe, expect, it } from "vitest";
import {
  deciderConfigFile,
  deciderConfigFileFromJson,
  deciderFromJson,
  deciderKindFromJson,
  deciderLabel,
  deciderLabelFromJson,
  deciderToJson,
  decideCommand,
  type Decider,
  type DeciderJson,
} from "../src/index.js";

// Every DeciderConfig variant in Lean's `Main.lean`. If a variant is added/renamed in Lean,
// this list (and the round-trip below) must be updated — that is the intended failure signal.
const ALL_DECIDERS: Decider[] = [
  { kind: "translatedCycler", n: 300 },
  { kind: "cycler", n: 107 },
  { kind: "explore", n: 130 },
  { kind: "loop1", n: 4100 },
  { kind: "backwardsReasoning", n: 5 },
  { kind: "nGramCPS", n: 2, bound: 200 },
  { kind: "nGramCPSHistory", history: 6, left: 3, right: 3, bound: 3200 },
  { kind: "nGramCPSLRU", left: 3, right: 3, bound: 20000 },
  { kind: "repWL", len: 4, threshold: 3, maxT: 320, bound: 2000 },
  { kind: "bb5TableExecutable" },
  { kind: "bb5TableAll" },
];

describe("decider attribution", () => {
  it("serializes to Lean DeciderConfig JSON", () => {
    expect(deciderToJson({ kind: "cycler", n: 107 })).toEqual({ cycler: 107 });
    expect(deciderToJson({ kind: "repWL", len: 4, threshold: 3, maxT: 320, bound: 2000 })).toEqual(
      { repWL: { len: 4, threshold: 3, maxT: 320, bound: 2000 } },
    );
    expect(deciderToJson({ kind: "bb5TableExecutable" })).toBe("bb5TableExecutable");
  });

  it("labels match Lean ToString", () => {
    expect(deciderLabel({ kind: "nGramCPS", n: 2, bound: 200 })).toBe("NGram CPS n=2 bound=200");
    expect(
      deciderLabel({ kind: "nGramCPSHistory", history: 2, left: 3, right: 3, bound: 1600 }),
    ).toBe("NGram CPS history=2 left=3 right=3 bound=1600");
  });

  it("builds a reproducible command and config file", () => {
    const d: Decider = { kind: "repWL", len: 4, threshold: 3, maxT: 320, bound: 2000 };
    expect(decideCommand("1RB1LB_1LA---")).toBe("lake exe beaver decide 1RB1LB_1LA--- --config decider.json");
    expect(JSON.parse(deciderConfigFile(d))).toEqual([{ repWL: { len: 4, threshold: 3, maxT: 320, bound: 2000 } }]);
  });

  it("every variant round-trips JSON <-> Decider and has a label", () => {
    for (const d of ALL_DECIDERS) {
      const j = deciderToJson(d);
      expect(deciderFromJson(j)).toEqual(d); // structural round-trip
      expect(deciderLabelFromJson(j)).toBe(deciderLabel(d)); // resilient label matches strict
      expect(JSON.parse(deciderConfigFileFromJson(j))).toEqual([j]); // raw passthrough config
    }
  });

  it("degrades gracefully on an unknown/new Lean variant (no throw)", () => {
    const unknown = { skeletBinaryCounter: { foo: 1 } } as unknown as DeciderJson;
    expect(() => deciderLabelFromJson(unknown)).not.toThrow();
    expect(deciderLabelFromJson(unknown)).toBe("skeletBinaryCounter");
    expect(deciderKindFromJson(unknown)).toBe("skeletBinaryCounter");
    // Config file still reproduces it verbatim.
    expect(JSON.parse(deciderConfigFileFromJson(unknown))).toEqual([unknown]);
    const unknownString = "newTableVariant" as unknown as DeciderJson;
    expect(deciderLabelFromJson(unknownString)).toBe("newTableVariant");
  });
});
