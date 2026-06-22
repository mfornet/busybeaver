import { describe, expect, it } from "vitest";
import {
  deciderConfigFile,
  deciderLabel,
  deciderToJson,
  decideCommand,
  type Decider,
} from "../src/index.js";

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
});
