import type { Verdict } from "../api.js";

const LABEL: Record<Verdict, string> = {
  halt: "Halts",
  loop: "Loops",
  undecided: "Holdout",
};

export function VerdictBadge({ verdict }: { verdict: Verdict }) {
  return <span className={`badge badge-${verdict}`}>{LABEL[verdict]}</span>;
}
