import { fileURLToPath } from "node:url";
import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// Base path for GitHub Pages project sites (e.g. "/busybeaver/"). Override with VITE_BASE.
const base = process.env.VITE_BASE ?? "/";

export default defineConfig({
  base,
  plugins: [react()],
  resolve: {
    alias: {
      // Resolve the core library to its TypeScript source for instant HMR and no prebuild.
      "@bb/core": fileURLToPath(new URL("../packages/core/src/index.ts", import.meta.url)),
    },
  },
  build: { target: "es2022", sourcemap: true },
});
