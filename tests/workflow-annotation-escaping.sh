#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Ensure paths controlled by a PR cannot inject additional workflow commands.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

for format in a2ml k9.ncl; do
  dir="$tmp/$format"
  mkdir -p "$dir"
  file="$dir/ordinary"$'\n'"::error::forged-command.$format"
  printf 'invalid fixture\n' > "$file"
  set +e
  if [[ "$format" == a2ml ]]; then
    INPUT_PATH="$dir" GITHUB_OUTPUT=/dev/null bash "$root/.githooks/validate-a2ml.sh" > "$tmp/$format.log" 2>&1
  else
    INPUT_PATH="$dir" GITHUB_OUTPUT=/dev/null bash "$root/.githooks/validate-k9.sh" > "$tmp/$format.log" 2>&1
  fi
  status=$?
  set -e
  [[ $status -ne 0 ]] || { echo "FAIL: invalid $format fixture passed" >&2; exit 1; }
  grep -Fq '%0A%3A%3Aerror%3A%3Aforged-command' "$tmp/$format.log"
  if grep -Fqx "::error::forged-command.$format" "$tmp/$format.log"; then
    echo "FAIL: $format file path injected a workflow command" >&2
    exit 1
  fi
done

echo 'workflow annotation escaping tests passed'
