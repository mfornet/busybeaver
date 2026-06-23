import { useEffect, useMemo, useState } from "react";
import { Link, useParams } from "react-router-dom";
import { INTERACTIVE_CANON_STEPS, canonicalize, simulate, tryParseMachine } from "@bb/core";
import { ApiError, api, type MachineRow } from "../api.js";
import { VerdictBadge } from "../components/Badge.js";
import { SpaceTime } from "../components/SpaceTime.js";
import { TransitionTable } from "../components/TransitionTable.js";
import { DecideCommand } from "../components/DecideCommand.js";

type DbState =
  | { kind: "loading" }
  | { kind: "found"; row: MachineRow }
  | { kind: "missing" }
  | { kind: "error"; message: string };

export function MachineView() {
  const { code: rawCode } = useParams();
  const code = decodeURIComponent(rawCode ?? "");
  const machine = useMemo(() => tryParseMachine(code), [code]);
  // Bound work on the render path (see INTERACTIVE_CANON_STEPS): covers the enumeration's
  // reachability horizon so the canonical code still matches the DB key, while a pathological
  // non-halting paste can't run the canonicalizer for its full default budget here.
  const canon = useMemo(
    () => (machine ? canonicalize(machine, { maxSteps: INTERACTIVE_CANON_STEPS }) : null),
    [machine],
  );
  const localRun = useMemo(
    () => (machine ? simulate(machine, 50_000) : null),
    [machine],
  );

  const [db, setDb] = useState<DbState>({ kind: "loading" });

  useEffect(() => {
    if (!canon) return;
    setDb({ kind: "loading" });
    api
      .machine(canon.code)
      .then((row) => setDb({ kind: "found", row }))
      .catch((e) => {
        if (e instanceof ApiError && e.status === 404) setDb({ kind: "missing" });
        else setDb({ kind: "error", message: String(e) });
      });
  }, [canon?.code]);

  if (!machine || !canon) {
    return (
      <div className="machineview">
        <div className="crumbs">
          <Link to="/">Home</Link> / invalid
        </div>
        <p className="error">Could not parse “{code}”.</p>
      </div>
    );
  }

  const rewritten = !canon.inputInTNF;

  return (
    <div className="machineview">
      <div className="crumbs">
        <Link to="/">Home</Link> /{" "}
        <Link to={`/size/${machine.nStates}/${machine.nSymbols}`}>
          BB({machine.nStates},{machine.nSymbols})
        </Link>{" "}
        / machine
      </div>

      <h1 className="mono machine-code">{canon.code}</h1>

      {rewritten && (
        <div className="banner">
          Rewritten to Tree Normal Form{canon.reflected ? " (with a left/right reflection)" : ""}.
          You entered <code className="mono">{code}</code>, which is equivalent to the canonical
          machine above.
        </div>
      )}

      <section className="grid2">
        <div>
          <h2>Transition table</h2>
          <TransitionTable machine={canon.machine} />
          <ul className="facts">
            <li>{machine.nStates} states · {machine.nSymbols} symbols</li>
            <li>{canon.reachableStates} states reachable from start</li>
            <li>
              Local simulation:{" "}
              {localRun!.status === "halt"
                ? `halts after ${localRun!.steps.toLocaleString()} steps`
                : `still running at ${localRun!.steps.toLocaleString()} steps`}
            </li>
          </ul>
        </div>

        <div>
          <h2>Decision</h2>
          <DbPanel db={db} code={canon.code} />
        </div>
      </section>

      <section>
        <h2>Space-time diagram</h2>
        <SpaceTime machine={canon.machine} />
      </section>
    </div>
  );
}

function DbPanel({ db, code }: { db: DbState; code: string }) {
  if (db.kind === "loading") return <p className="muted">Looking up verdict…</p>;
  if (db.kind === "error") return <p className="error">{db.message}</p>;
  if (db.kind === "missing") {
    return (
      <div className="notindb">
        <p>
          This machine is not in the enumerated database (it may be larger than BB(5,2), or not a
          canonical leaf of the enumeration). You can still run a decider on it yourself:
        </p>
        <pre className="mono">lake exe beaver decide {code}</pre>
      </div>
    );
  }
  const { row } = db;
  return (
    <div className="dbpanel">
      <div className="dbpanel-head">
        <VerdictBadge verdict={row.verdict} />
        {row.steps != null && <span className="muted">halts in {row.steps.toLocaleString()}</span>}
        <span className="muted">enumeration #{row.ordinal.toLocaleString()}</span>
      </div>
      {row.decider ? (
        <DecideCommand code={row.code} decider={row.decider} />
      ) : (
        <p className="muted">
          Open holdout — no decider in the current pipeline settles this machine yet.
        </p>
      )}
    </div>
  );
}
