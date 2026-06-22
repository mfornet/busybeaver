import { type Machine, serializeStmt, stateLetter } from "@bb/core";

/** Render the transition table: rows = states, columns = symbols. */
export function TransitionTable({ machine }: { machine: Machine }) {
  return (
    <table className="ttable">
      <thead>
        <tr>
          <th />
          {Array.from({ length: machine.nSymbols }, (_, sym) => (
            <th key={sym}>read {sym}</th>
          ))}
        </tr>
      </thead>
      <tbody>
        {machine.table.map((row, state) => (
          <tr key={state}>
            <th>{stateLetter(state)}</th>
            {row.map((stmt, sym) => (
              <td key={sym} className={stmt.kind === "halt" ? "halt-cell" : ""}>
                <code>{serializeStmt(stmt)}</code>
              </td>
            ))}
          </tr>
        ))}
      </tbody>
    </table>
  );
}
