import { useState } from "react";
import {
  type DeciderJson,
  deciderConfigFileFromJson,
  deciderLabelFromJson,
  decideCommand,
} from "@bb/core";

function Copy({ text }: { text: string }) {
  const [done, setDone] = useState(false);
  return (
    <button
      className="copy"
      onClick={async () => {
        await navigator.clipboard.writeText(text);
        setDone(true);
        setTimeout(() => setDone(false), 1200);
      }}
    >
      {done ? "copied" : "copy"}
    </button>
  );
}

/**
 * Show the exact, reproducible command the user can run in the Lean project to watch the
 * stored decider decide this machine: write the one-decider config, then `beaver decide`.
 */
export function DecideCommand({ code, decider }: { code: string; decider: DeciderJson }) {
  // Built from the raw JSON so an unknown/new Lean decider still renders (no crash).
  const configFile = deciderConfigFileFromJson(decider);
  const command = decideCommand(code);

  return (
    <div className="decide">
      <p>
        Decided by <strong>{deciderLabelFromJson(decider)}</strong>. Reproduce it in the{" "}
        <a href="https://github.com/mfornet/busybeaver">Lean project</a>:
      </p>
      <div className="codeblock">
        <div className="codeblock-head">
          <span>decider.json</span>
          <Copy text={configFile} />
        </div>
        <pre>{configFile}</pre>
      </div>
      <div className="codeblock">
        <div className="codeblock-head">
          <span>shell</span>
          <Copy text={command} />
        </div>
        <pre>{command}</pre>
      </div>
    </div>
  );
}
