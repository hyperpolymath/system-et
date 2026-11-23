#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/input"

check_pedigree() {
  local expected="$1" message="$2" status=0
  shift 2
  printf 'K9!\n# SPDX-License-Identifier: MPL-2.0\n%s' "$*" > "$tmp/input/fixture.k9.ncl"
  INPUT_STRICT=true INPUT_PATH="$tmp/input" INPUT_PATHS_IGNORE= GITHUB_OUTPUT=/dev/null \
    bash "$root/.githooks/validate-k9.sh" > "$tmp/result" || status=$?
  if [[ "$status" != "$expected" ]] || ! grep -Fq "$message" "$tmp/result"; then
    cat "$tmp/result" >&2
    return 1
  fi
}

check_pedigree 0 'K9 validation passed' \
  "pedigree = component_pedigree & { name = \"test, # example\", schema_version = \"1\", leash = 'YaRd }"
check_pedigree 0 'K9 validation passed' \
  'pedigree = { name = "test", version = "1", leash = "Hunt", signature_required = true }'
check_pedigree 1 'Hunt-level K9 file must include' \
  'pedigree = { name = "test", version = "1", leash = "Hunt" } # signature = "absent"'
check_pedigree 1 "Invalid security level 'unknown'" \
  'pedigree = { name = "test", version = "1", leash = "Unknown" }'
check_pedigree 1 "missing 'name' field" \
  $'pedigree = {\n  # name = "comment"\n  version = "1",\n  leash = "Kennel",\n}'
check_pedigree 1 "missing 'version' or 'schema_version'" \
  $'pedigree = {\n  name = "test", # version = "comment"\n  leash = "Kennel",\n}'
check_pedigree 0 'K9 validation passed' \
  $'pedigree = {\n  security = {\n    leash = "Kennel",\n  }, # }\n  metadata = {\n    name = "test",\n    version = "1",\n  },\n}'

echo 'K9 pedigree validation tests passed'
