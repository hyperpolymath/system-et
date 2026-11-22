#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Check tracked-source/document extensions for invisible control/format characters.
# Exit: 0 = scan completed and clean; 1 = findings or scanner/infrastructure error.
set -euo pipefail
root="${1:-.}"
[[ -d "$root" ]] || { echo "::error::invisible-character scan path is not a directory: $root"; exit 1; }

patterns='(*UTF)[\x00-\x08\x0B\x0C\x0E-\x1F\x{a0}\x{ad}\x{200b}-\x{200f}\x{202a}-\x{202f}\x{2060}\x{2066}-\x{2069}\x{feff}]'
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# Capture discovery errors distinctly from grep's normal "no match" exit 1.
find "$root" \
  -not -path '*/.git/*' -not -path '*/node_modules/*' \
  -not -path '*/.deno/*' -not -path '*/target/*' \
  -not -path '*/_build/*' -not -path '*/deps/*' \
  -not -path '*/external_corpora/*' -not -path '*/.lake/*' \
  -type f \( -name '*.rs' -o -name '*.ex' -o -name '*.exs' -o -name '*.res' \
    -o -name '*.js' -o -name '*.ts' -o -name '*.json' -o -name '*.toml' \
    -o -name '*.yml' -o -name '*.yaml' -o -name '*.md' -o -name '*.adoc' \
    -o -name '*.idr' -o -name '*.zig' -o -name '*.v' -o -name '*.jl' \
    -o -name '*.gleam' -o -name '*.hs' -o -name '*.ml' -o -name '*.sh' \) \
  -print0 > "$tmp/candidates"

: > "$tmp/findings"
while IFS= read -r -d '' file; do
  if grep -aPl -- "$patterns" "$file" >/dev/null; then
    printf '%s\0' "$file" >> "$tmp/findings"
  else
    status=$?
    if [[ $status -ne 1 ]]; then
      echo "::error::invisible-character scanner failed on a candidate file (grep exit $status)"
      exit 1
    fi
  fi
done < "$tmp/candidates"

mapfile -d '' -t findings < "$tmp/findings"
if [[ ${#findings[@]} -gt 0 ]]; then
  echo "::error::invisible-character scan found ${#findings[@]} file(s) with prohibited characters"
  # %q keeps control characters on one line; the fixed prefix keeps paths as data.
  printf '  file: %q\n' "${findings[@]}"
  if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    {
      echo '## Invisible-character scan — blocked'
      echo
      echo "Found **${#findings[@]}** affected file(s):"
      for file in "${findings[@]}"; do printf -- "- \`%q\`\n" "$file"; done
    } >> "$GITHUB_STEP_SUMMARY"
  fi
  exit 1
fi

echo 'invisible-character scan completed: no prohibited characters found'
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  printf '%s\n' '## Invisible-character scan' '' 'No prohibited characters found.' >> "$GITHUB_STEP_SUMMARY"
fi
