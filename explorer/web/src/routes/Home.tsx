import { useEffect, useState } from "react";
import { Link } from "react-router-dom";
import { api, type Summary } from "../api.js";

function pct(n: number, total: number): string {
  return total === 0 ? "0%" : `${((100 * n) / total).toFixed(total > 1000 ? 2 : 0)}%`;
}

function SizeCard({ s }: { s: Summary["sizes"][number] }) {
  const decided = s.n_halt + s.n_nonhalt;
  return (
    <Link className="sizecard" to={`/size/${s.states}/${s.symbols}`}>
      <div className="sizecard-title">
        BB({s.states},{s.symbols})
      </div>
      <div className="sizecard-total">{s.total.toLocaleString()} machines</div>
      <div className="bar">
        <span className="seg seg-halt" style={{ width: pct(s.n_halt, s.total) }} />
        <span className="seg seg-nonhalt" style={{ width: pct(s.n_nonhalt, s.total) }} />
        <span className="seg seg-undecided" style={{ width: pct(s.n_undecided, s.total) }} />
      </div>
      <div className="sizecard-stats">
        <span>{s.n_halt.toLocaleString()} halt</span>
        <span>{s.n_nonhalt.toLocaleString()} non-halt</span>
        <span>{s.n_undecided.toLocaleString()} holdout</span>
      </div>
      <div className="sizecard-foot">
        {s.decided_fully ? (
          <span className="ok">
            ✓ fully decided · BB = {s.max_steps?.toLocaleString() ?? "?"}
          </span>
        ) : (
          <span className="pending">{pct(decided, s.total)} decided</span>
        )}
      </div>
    </Link>
  );
}

export function Home() {
  const [summary, setSummary] = useState<Summary | null>(null);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    api.summary().then(setSummary).catch((e) => setError(String(e)));
  }, []);

  return (
    <div className="home">
      <section className="hero">
        <h1>The Busy Beaver formalization, machine by machine</h1>
        <p>
          Every Turing machine below is enumerated in{" "}
          <a href="https://wiki.bbchallenge.org/wiki/Tree_Normal_Form">Tree Normal Form</a> and
          classified by the formal deciders in the Lean project. Browse the decided machines and
          the remaining holdouts, or paste any machine to see its behavior and how it was settled.
        </p>
      </section>

      {error && <p className="error">Could not load summary: {error}</p>}
      {!summary && !error && <p className="muted">Loading…</p>}

      {summary && (
        <>
          <section className="ladder">
            {summary.sizes.map((s) => (
              <SizeCard key={`${s.states}-${s.symbols}`} s={s} />
            ))}
            {summary.sizes.length === 0 && (
              <p className="muted">No data ingested yet.</p>
            )}
          </section>

          {summary.deciders.length > 0 && (
            <section className="deciders">
              <h2>How machines were decided</h2>
              <DeciderBreakdown summary={summary} />
            </section>
          )}
        </>
      )}
    </div>
  );
}

function DeciderBreakdown({ summary }: { summary: Summary }) {
  // Aggregate decider counts across all sizes.
  const totals = new Map<string, number>();
  for (const d of summary.deciders) {
    totals.set(d.decider_kind, (totals.get(d.decider_kind) ?? 0) + d.n);
  }
  const rows = [...totals.entries()].sort((a, b) => b[1] - a[1]);
  const max = rows[0]?.[1] ?? 1;
  return (
    <div className="breakdown">
      {rows.map(([kind, n]) => (
        <div className="breakdown-row" key={kind}>
          <span className="breakdown-label">{kind}</span>
          <span className="breakdown-bar">
            <span style={{ width: `${(100 * n) / max}%` }} />
          </span>
          <span className="breakdown-count">{n.toLocaleString()}</span>
        </div>
      ))}
    </div>
  );
}
