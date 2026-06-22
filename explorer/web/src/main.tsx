import React from "react";
import { createRoot } from "react-dom/client";
import { HashRouter, Route, Routes, Navigate } from "react-router-dom";
import { App } from "./App.js";
import { Home } from "./routes/Home.js";
import { SizeView } from "./routes/SizeView.js";
import { MachineView } from "./routes/MachineView.js";
import "./styles.css";

createRoot(document.getElementById("root")!).render(
  <React.StrictMode>
    {/* HashRouter keeps deep links working on GitHub Pages without server rewrites. */}
    <HashRouter>
      <Routes>
        <Route path="/" element={<App />}>
          <Route index element={<Home />} />
          <Route path="size/:states/:symbols" element={<SizeView />} />
          <Route path="machine/:code" element={<MachineView />} />
          <Route path="*" element={<Navigate to="/" replace />} />
        </Route>
      </Routes>
    </HashRouter>
  </React.StrictMode>,
);
