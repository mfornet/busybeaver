import { useState } from "react";
import { useNavigate } from "react-router-dom";
import { INTERACTIVE_CANON_STEPS, canonicalize, tryParseMachine } from "@bb/core";

/** Paste any machine code; we canonicalize to TNF and navigate to its detail page. */
export function MachineSearch() {
  const [value, setValue] = useState("");
  const [error, setError] = useState<string | null>(null);
  const navigate = useNavigate();

  function submit(e: React.FormEvent) {
    e.preventDefault();
    const machine = tryParseMachine(value);
    if (!machine) {
      setError("Could not parse that machine code");
      return;
    }
    setError(null);
    // Navigate by canonical TNF code so equivalent inputs land on the same page.
    // Bounded budget keeps the submit handler responsive even for non-halting pastes.
    const { code } = canonicalize(machine, { maxSteps: INTERACTIVE_CANON_STEPS });
    navigate(`/machine/${encodeURIComponent(code)}`);
    setValue("");
  }

  return (
    <form className="search" onSubmit={submit}>
      <input
        aria-label="Machine code"
        spellCheck={false}
        placeholder="Paste a machine, e.g. 1RB1LB_1LA---"
        value={value}
        onChange={(e) => {
          setValue(e.target.value);
          setError(null);
        }}
      />
      <button type="submit">Explore</button>
      {error && <span className="search-error">{error}</span>}
    </form>
  );
}
