import { Link, Outlet } from "react-router-dom";
import { MachineSearch } from "./components/MachineSearch.js";

export function App() {
  return (
    <div className="app">
      <header className="topbar">
        <Link to="/" className="brand">
          <span className="logo">🦫</span>
          <span>Busy Beaver Explorer</span>
        </Link>
        <MachineSearch />
        <a
          className="ghlink"
          href="https://github.com/mfornet/busybeaver"
          target="_blank"
          rel="noreferrer"
        >
          Lean formalization ↗
        </a>
      </header>
      <main className="content">
        <Outlet />
      </main>
      <footer className="footer">
        <span>
          A downstream view of the{" "}
          <a href="https://github.com/mfornet/busybeaver">Lean Busy Beaver</a> project. Verdicts
          are produced by the formal deciders; this site only displays them.
        </span>
      </footer>
    </div>
  );
}
