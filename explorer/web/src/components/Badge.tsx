import { type Verdict, VERDICT_LABEL } from "../api.js";

export function VerdictBadge({ verdict }: { verdict: Verdict }) {
  return <span className={`badge badge-${verdict}`}>{VERDICT_LABEL[verdict]}</span>;
}
