#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
scanner="$root/scripts/check-invisible-characters.sh"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/clean" "$tmp/dirty"
printf 'ordinary text\n' > "$tmp/clean/ok.adoc"
printf 'ordinary source\n' > "$tmp/clean/ok.rs"
bash "$scanner" "$tmp/clean" > "$tmp/clean.log"
grep -Fq 'no prohibited characters' "$tmp/clean.log"

# NBSP is intentionally a literal U+00A0 character in this fixture.
printf 'a\302\240b\n' > "$tmp/dirty/bad.rs"
if bash "$scanner" "$tmp/dirty" > "$tmp/dirty.log" 2>&1; then
  echo 'FAIL: scanner accepted a source file containing NBSP' >&2
  exit 1
fi
grep -Fq 'found 1 file(s)' "$tmp/dirty.log"
grep -Fq 'bad.rs' "$tmp/dirty.log"

if bash "$scanner" "$tmp/missing" > "$tmp/missing.log" 2>&1; then
  echo 'FAIL: scanner accepted a missing scan root' >&2
  exit 1
fi
grep -Fq 'not a directory' "$tmp/missing.log"
echo 'invisible-character scanner tests passed'
