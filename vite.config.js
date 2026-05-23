import { defineConfig } from "vite";
import { resolve } from "path";

// Multi-page app: each HTML file dispatches to the right Fable entry
// (src/main.fs.js) based on the URL. Static assets live in ./public
// and are served at the root (e.g. /data/..., /demos/...).
export default defineConfig({
  server: { port: 8080 },
  build: {
    outDir: "dist",
    rollupOptions: {
      input: {
        main: resolve(__dirname, "index.html"),
        webnicek: resolve(__dirname, "webnicek.html"),
        datnicek: resolve(__dirname, "datnicek.html"),
        essay: resolve(__dirname, "essay.html"),
      },
    },
  },
});
