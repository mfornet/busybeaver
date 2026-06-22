/** Typed client for the read-only explorer API. */
import type { DeciderJson } from "@bb/core";

// Configured at build time. Falls back to same-origin "/api" for local proxying.
const API_BASE = (import.meta.env.VITE_API_BASE as string | undefined)?.replace(/\/$/, "") ?? "";

// Canonical verdict vocabulary (mirrors the `verdict` enum in db/schema.sql). 'nonhalt' is
// "proven not to halt" by any decider — not necessarily a periodic cycler — so its label is
// "Non-halting", not "Loops".
export const VERDICTS = ["halt", "nonhalt", "undecided"] as const;
export type Verdict = (typeof VERDICTS)[number];
export const VERDICT_LABEL: Record<Verdict, string> = {
  halt: "Halts",
  nonhalt: "Non-halting",
  undecided: "Holdout",
};

export interface MachineRow {
  code: string;
  states: number;
  symbols: number;
  ordinal: number;
  verdict: Verdict;
  steps: number | null;
  decider: DeciderJson | null;
  decider_kind: string | null;
}

export interface MachinePage {
  machines: MachineRow[];
  next_cursor: number | null;
}

export interface SizeSummary {
  states: number;
  symbols: number;
  total: number;
  n_halt: number;
  n_nonhalt: number;
  n_undecided: number;
  max_steps: number | null;
  decided_fully: boolean;
}

export interface DeciderCount {
  states: number;
  symbols: number;
  decider_kind: string;
  n: number;
}

export interface Summary {
  sizes: SizeSummary[];
  deciders: DeciderCount[];
}

export interface SizeDetail {
  summary: SizeSummary;
  deciders: DeciderCount[];
}

export class ApiError extends Error {
  constructor(public status: number, message: string) {
    super(message);
  }
}

async function get<T>(path: string): Promise<T> {
  const res = await fetch(`${API_BASE}${path}`);
  if (!res.ok) throw new ApiError(res.status, `${res.status} on ${path}`);
  return (await res.json()) as T;
}

export const api = {
  /** Landing summary. Falls back to a prebuilt static file if the API is unreachable. */
  async summary(): Promise<Summary> {
    try {
      return await get<Summary>("/api/summary");
    } catch {
      return await get<Summary>(`${import.meta.env.BASE_URL}summary.json`);
    }
  },
  sizeDetail(states: number, symbols: number): Promise<SizeDetail> {
    return get<SizeDetail>(`/api/sizes/${states}/${symbols}/summary`);
  },
  machines(params: {
    states: number;
    symbols: number;
    verdict?: Verdict;
    decider_kind?: string;
    after_ordinal?: number;
    limit?: number;
  }): Promise<MachinePage> {
    const q = new URLSearchParams();
    q.set("states", String(params.states));
    q.set("symbols", String(params.symbols));
    if (params.verdict) q.set("verdict", params.verdict);
    if (params.decider_kind) q.set("decider_kind", params.decider_kind);
    if (params.after_ordinal != null) q.set("after_ordinal", String(params.after_ordinal));
    if (params.limit != null) q.set("limit", String(params.limit));
    return get<MachinePage>(`/api/machines?${q.toString()}`);
  },
  machine(code: string): Promise<MachineRow> {
    return get<MachineRow>(`/api/machines/${encodeURIComponent(code)}`);
  },
};
