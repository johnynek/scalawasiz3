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
