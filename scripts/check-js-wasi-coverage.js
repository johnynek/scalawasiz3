#!/usr/bin/env node

const fs = require("node:fs");

const supportedImports = new Set([
  "args_get",
  "args_sizes_get",
  "environ_get",
  "environ_sizes_get",
  "fd_read",
  "fd_write",
  "fd_close",
  "fd_fdstat_get",
  "fd_seek",
  "fd_tell",
  "clock_res_get",
  "clock_time_get",
  "random_get",
  "proc_exit",
  "sched_yield",
  "fd_advise",
  "fd_allocate",
  "fd_datasync",
  "fd_fdstat_set_flags",
  "fd_fdstat_set_rights",
  "fd_filestat_get",
  "fd_filestat_set_size",
  "fd_filestat_set_times",
  "fd_pread",
  "fd_prestat_dir_name",
  "fd_prestat_get",
  "fd_pwrite",
  "fd_readdir",
  "fd_renumber",
  "fd_sync",
  "path_create_directory",
  "path_filestat_get",
  "path_filestat_set_times",
  "path_link",
  "path_open",
  "path_readlink",
  "path_remove_directory",
  "path_rename",
  "path_symlink",
  "path_unlink_file",
  "poll_oneoff",
  "proc_raise",
  "sock_accept",
  "sock_recv",
  "sock_send",
  "sock_shutdown",
]);

function loadImportsFromWasm(wasmPath) {
  const bytes = fs.readFileSync(wasmPath);
  const mod = new WebAssembly.Module(bytes);
  return WebAssembly.Module.imports(mod)
    .filter((imp) => imp.module === "wasi_snapshot_preview1")
    .map((imp) => imp.name);
}

function main() {
  const wasmPath = process.argv[2];
  if (!wasmPath) {
    console.error("usage: check-js-wasi-coverage.js <z3.wasm>");
    process.exit(1);
  }

  const required = loadImportsFromWasm(wasmPath);
  const missing = required.filter((name) => !supportedImports.has(name));

  if (missing.length > 0) {
    console.error("Missing JS WASI handlers for imports:");
    for (const name of missing) {
      console.error(`- ${name}`);
    }
    process.exit(2);
  }

  console.log(`JS WASI coverage check passed. Required imports: ${required.length}`);
}

main();
