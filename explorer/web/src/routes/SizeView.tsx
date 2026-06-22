import { useCallback, useEffect, useRef, useState } from "react";
import { Link, useParams, useSearchParams } from "react-router-dom";
import { api, type MachineRow, type SizeDetail, type Verdict, VERDICTS, VERDICT_LABEL } from "../api.js";
import { VerdictBadge } from "../components/Badge.js";

const PAGE = 100;

export function SizeView() {
  const { states: statesP, symbols: symbolsP } = useParams();
  const states = Number(statesP);
  const symbols = Number(symbolsP);
  const [params, setParams] = useSearchParams();
  const verdict = (params.get("verdict") as Verdict | null) ?? undefined;
  const deciderKind = params.get("decider") ?? undefined;

  const [detail, setDetail] = useState<SizeDetail | null>(null);
  const [rows, setRows] = useState<MachineRow[]>([]);
  const [cursor, setCursor] = useState<number | null>(-1);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const reqId = useRef(0);

  useEffect(() => {
    api.sizeDetail(states, symbols).then(setDetail).catch(() => setDetail(null));
  }, [states, symbols]);

  const load = useCallback(
    async (after: number, reset: boolean) => {
      const id = ++reqId.current;
      setLoading(true);
      setError(null);
      try {
        const page = await api.machines({
          states, symbols, verdict, decider_kind: deciderKind, after_ordinal: after, limit: PAGE,
        });
        if (id !== reqId.current) return; // stale response
        setRows((prev) => (reset ? page.machines : [...prev, ...page.machines]));
        setCursor(page.next_cursor);
      } catch (e) {
        if (id === reqId.current) setError(String(e));
      } finally {
        if (id === reqId.current) setLoading(false);
      }
    },
    [states, symbols, verdict, deciderKind],
  );

  // Reload from the start whenever size or filters change.
  useEffect(() => {
    setRows([]);
    setCursor(-1);
    load(-1, true);
  }, [load]);

  function setFilter(key: "verdict" | "decider", value: string | undefined) {
    const next = new URLSearchParams(params);
    if (value) next.set(key, value);
    else next.delete(key);
    setParams(next, { replace: true });
  }

  return (
    <div className="sizeview">
      <div className="crumbs">
        <Link to="/">Home</Link> / BB({states},{symbols})
      </div>

      {detail && (
        <div className="sizehead">
          <h1>BB({states},{symbols})</h1>
          <div className="sizehead-stats">
            <span>{detail.summary.total.toLocaleString()} machines</span>
            <span>{detail.summary.n_halt.toLocaleString()} halt</span>
            <span>{detail.summary.n_nonhalt.toLocaleString()} non-halt</span>
            <span>{detail.summary.n_undecided.toLocaleString()} holdout</span>
            {detail.summary.decided_fully && (
              <span className="ok">BB = {detail.summary.max_steps?.toLocaleString()}</span>
            )}
          </div>
        </div>
      )}

      <div className="filters">
        <div className="filtergroup">
          <span>Verdict:</span>
          {VERDICTS.map((v) => (
            <button
              key={v}
              className={verdict === v ? "chip active" : "chip"}
              onClick={() => setFilter("verdict", verdict === v ? undefined : v)}
            >
              {VERDICT_LABEL[v]}
            </button>
          ))}
        </div>
        {detail && detail.deciders.length > 0 && (
          <div className="filtergroup">
            <span>Decider:</span>
            {detail.deciders.map((d) => (
              <button
                key={d.decider_kind}
                className={deciderKind === d.decider_kind ? "chip active" : "chip"}
                onClick={() =>
                  setFilter("decider", deciderKind === d.decider_kind ? undefined : d.decider_kind)
                }
              >
                {d.decider_kind} ({d.n.toLocaleString()})
              </button>
            ))}
          </div>
        )}
      </div>

      {error && <p className="error">{error}</p>}

      <table className="machine-list">
        <thead>
          <tr>
            <th>#</th>
            <th>machine</th>
            <th>verdict</th>
            <th>steps</th>
            <th>decided by</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((m) => (
            <tr key={m.code}>
              <td className="muted">{m.ordinal.toLocaleString()}</td>
              <td>
                <Link className="mono" to={`/machine/${encodeURIComponent(m.code)}`}>
                  {m.code}
                </Link>
              </td>
              <td>
                <VerdictBadge verdict={m.verdict} />
              </td>
              <td className="mono">{m.steps?.toLocaleString() ?? "—"}</td>
              <td className="muted">{m.decider_kind ?? "—"}</td>
            </tr>
          ))}
        </tbody>
      </table>

      {rows.length === 0 && !loading && <p className="muted">No machines match.</p>}

      <div className="loadmore">
        {cursor !== null ? (
          <button disabled={loading} onClick={() => load(cursor, false)}>
            {loading ? "Loading…" : "Load more"}
          </button>
        ) : (
          rows.length > 0 && <span className="muted">End of list.</span>
        )}
      </div>
    </div>
  );
}
