#!/usr/bin/env bash
set -euo pipefail

workflow_file="${1:-.github/workflows/release.yml}"

if [[ ! -f "$workflow_file" ]]; then
  echo "missing workflow file: $workflow_file" >&2
  exit 1
fi

# Extract the `on.push` block so we only validate push trigger keys.
push_block="$({
  awk '
    /^on:/ { in_on = 1; next }
    in_on && /^[^[:space:]]/ { in_on = 0 }
    in_on { print }
  ' "$workflow_file"
} | awk '
  /^  push:/ { in_push = 1; next }
  in_push && /^  [^[:space:]]/ { in_push = 0 }
  in_push { print }
')"

if [[ -z "$push_block" ]]; then
  echo "release workflow is missing on.push trigger block" >&2
  exit 1
fi

if echo "$push_block" | grep -Eq '^[[:space:]]*branches:'; then
  echo "release workflow should not trigger on branch pushes" >&2
  exit 1
fi

if ! echo "$push_block" | grep -Eq '^[[:space:]]*tags:'; then
  echo "release workflow must trigger on tag pushes" >&2
  exit 1
fi

publish_step_block="$(
  awk '
    /^[[:space:]]*- name: Publish[[:space:]]*$/ { in_publish = 1; next }
    in_publish && /^[[:space:]]*- name:/ { in_publish = 0 }
    in_publish { print }
  ' "$workflow_file"
)"

if [[ -z "$publish_step_block" ]]; then
  echo "release workflow is missing the Publish step" >&2
  exit 1
fi

if ! echo "$publish_step_block" | grep -Eq "^[[:space:]]*if:[[:space:]]*startsWith\\(github\\.ref,[[:space:]]*'refs/tags/'\\)"; then
  echo "Publish step must be guarded to run only on tag refs" >&2
  exit 1
fi

validate_line="$(grep -n "name: Validate release tag and version" "$workflow_file" | head -n 1 | cut -d: -f1 || true)"
build_line="$(grep -n "name: Build Z3 WASI artifact" "$workflow_file" | head -n 1 | cut -d: -f1 || true)"
if [[ -z "$validate_line" || -z "$build_line" ]]; then
  echo "release workflow must include both validation and build steps" >&2
  exit 1
fi
if (( validate_line >= build_line )); then
  echo "release version validation must run before the long Z3 build step" >&2
  exit 1
fi

if ! grep -Eq "check-js-wasi-coverage\\.js[[:space:]]+core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3\\.wasm" "$workflow_file"; then
  echo "WASI import coverage must validate the runtime resource path used by JS/JVM packaging" >&2
  exit 1
fi

if ! grep -Eq "^[[:space:]]*core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3\\.wasm$" "$workflow_file"; then
  echo "GitHub release upload must include z3.wasm resource" >&2
  exit 1
fi

if ! grep -Eq "^[[:space:]]*core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3\\.wasm\\.sha256$" "$workflow_file"; then
  echo "GitHub release upload must include z3.wasm.sha256 resource" >&2
  exit 1
fi

if grep -Eq "OUT_WASM:[[:space:]]*\\$\\{\\{ env\\.RELEASE_ASSET_DIR \\}\\}/z3\\.wasm" "$workflow_file"; then
  echo "release workflow should build z3.wasm into the runtime resource path, not release-assets" >&2
  exit 1
fi

if grep -Eq "name:[[:space:]]*Ensure checked-in WASM resources are release-ready" "$workflow_file"; then
  echo "release workflow should not compare generated wasm against checked-in resources" >&2
  exit 1
fi

if grep -Eq 'cmp -s[[:space:]]+"\$built_wasm"[[:space:]]+"\$tracked_wasm"' "$workflow_file"; then
  echo "release workflow should not compare generated and checked-in z3.wasm" >&2
  exit 1
fi

if grep -Eq 'cmp -s[[:space:]]+"\$built_sha"[[:space:]]+"\$tracked_sha"' "$workflow_file"; then
  echo "release workflow should not compare generated and checked-in z3.wasm.sha256" >&2
  exit 1
fi
