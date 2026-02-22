#!/usr/bin/env node

const fs = require("node:fs");
const path = require("node:path");

function main() {
  const wasmPath = process.argv[2];
  const outPath = process.argv[3];

  if (!wasmPath) {
    console.error("usage: inspect-wasm-imports.js <wasm-path> [out-json-path]");
    process.exit(1);
  }

  const wasmBytes = fs.readFileSync(wasmPath);
  const mod = new WebAssembly.Module(wasmBytes);
  const imports = WebAssembly.Module.imports(mod).map((imp) => ({
    module: imp.module,
    name: imp.name,
    kind: imp.kind,
  }));

  const output = {
    wasm: path.resolve(wasmPath),
    importCount: imports.length,
    imports,
  };

  const json = JSON.stringify(output, null, 2);
  if (outPath) {
    fs.mkdirSync(path.dirname(outPath), { recursive: true });
    fs.writeFileSync(outPath, json);
  } else {
    process.stdout.write(`${json}\n`);
  }
}

main();
