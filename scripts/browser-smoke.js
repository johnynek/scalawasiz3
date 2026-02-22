#!/usr/bin/env node

const http = require("node:http");
const fs = require("node:fs");
const path = require("node:path");

const ROOT = path.resolve(__dirname, "..");
const WASM_PATH = "/core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm";

function contentType(filePath) {
  if (filePath.endsWith(".wasm")) return "application/wasm";
  if (filePath.endsWith(".js")) return "text/javascript";
  if (filePath.endsWith(".html")) return "text/html; charset=utf-8";
  return "application/octet-stream";
}

function createServer() {
  return http.createServer((req, res) => {
    const reqPath = decodeURIComponent(req.url.split("?")[0]);
    if (reqPath === "/__smoke__.html") {
      res.setHeader("content-type", "text/html; charset=utf-8");
      res.end("<!doctype html><html><body>smoke</body></html>");
      return;
    }

    const abs = path.resolve(ROOT, `.${reqPath}`);

    if (!abs.startsWith(ROOT)) {
      res.statusCode = 403;
      res.end("forbidden");
      return;
    }

    if (!fs.existsSync(abs) || fs.statSync(abs).isDirectory()) {
      res.statusCode = 404;
      res.end("not found");
      return;
    }

    res.setHeader("content-type", contentType(abs));
    fs.createReadStream(abs).pipe(res);
  });
}

async function main() {
  let playwright;
  try {
    playwright = require("playwright");
  } catch (_e) {
    console.error("playwright is not installed. Run: npm install --no-save playwright");
    process.exit(2);
  }

  const server = createServer();
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));

  const addr = server.address();
  const base = `http://127.0.0.1:${addr.port}`;

  const browser = await playwright.chromium.launch({ headless: true });
  const page = await browser.newPage();

  try {
    await page.goto(`${base}/__smoke__.html`);

    const result = await page.evaluate(async ({ wasmPath }) => {
      const resp = await fetch(wasmPath);
      if (!resp.ok) {
        return { ok: false, message: `fetch failed: ${resp.status}` };
      }

      const bytes = await resp.arrayBuffer();
      const mod = await WebAssembly.compile(bytes);
      const imports = WebAssembly.Module.imports(mod);
      return {
        ok: true,
        importCount: imports.length,
      };
    }, { wasmPath: WASM_PATH });

    if (!result.ok) {
      throw new Error(result.message);
    }

    console.log(`browser smoke passed; wasm import count=${result.importCount}`);
  } finally {
    await browser.close();
    server.close();
  }
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : String(err));
  process.exit(1);
});
