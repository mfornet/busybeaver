import { useEffect, useMemo, useRef, useState } from "react";
import { type Machine, spaceTimeDiagram } from "@bb/core";

// Symbol colors (index 0 = blank). Read from CSS variables so theming stays consistent.
function symbolColors(): string[] {
  const css = getComputedStyle(document.documentElement);
  const v = (name: string, fallback: string) =>
    css.getPropertyValue(name).trim() || fallback;
  return [
    v("--cell-0", "#f4f4f5"),
    v("--cell-1", "#2563eb"),
    v("--cell-2", "#f59e0b"),
    v("--cell-3", "#10b981"),
  ];
}

export function SpaceTime({ machine }: { machine: Machine }) {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const [maxSteps, setMaxSteps] = useState(400);

  const diagram = useMemo(() => spaceTimeDiagram(machine, { maxSteps }), [machine, maxSteps]);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const { width, height, symbols, heads } = diagram;

    // Fit within ~720px wide; keep cells at least 1px, at most 14px.
    const cell = Math.max(1, Math.min(14, Math.floor(720 / Math.max(1, width))));
    const dpr = window.devicePixelRatio || 1;
    const pxW = width * cell;
    const pxH = height * cell;
    canvas.width = pxW * dpr;
    canvas.height = pxH * dpr;
    canvas.style.width = `${pxW}px`;
    canvas.style.height = `${pxH}px`;

    const ctx = canvas.getContext("2d")!;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    const colors = symbolColors();

    for (let t = 0; t < height; t++) {
      const base = t * width;
      for (let c = 0; c < width; c++) {
        const sym = symbols[base + c]!;
        if (sym === 0 && cell > 1) continue; // leave blanks as background
        ctx.fillStyle = colors[sym] ?? colors[1]!;
        ctx.fillRect(c * cell, t * cell, cell, cell);
      }
      // Head marker.
      const hc = heads[t]!;
      if (hc >= 0 && hc < width) {
        ctx.fillStyle = "rgba(239,68,68,0.55)";
        ctx.fillRect(hc * cell, t * cell, Math.max(1, cell), Math.max(1, cell));
      }
    }
  }, [diagram]);

  return (
    <div className="spacetime">
      <div className="spacetime-controls">
        <label>
          Steps: <strong>{diagram.steps}</strong>
          {diagram.halted ? " (halted)" : " (running)"}
        </label>
        <input
          type="range"
          min={50}
          max={4000}
          step={50}
          value={maxSteps}
          onChange={(e) => setMaxSteps(Number(e.target.value))}
        />
        <span className="muted">render budget: {maxSteps}</span>
      </div>
      <div className="spacetime-canvas-wrap">
        <canvas ref={canvasRef} />
      </div>
    </div>
  );
}
