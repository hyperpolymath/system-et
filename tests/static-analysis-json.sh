#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
validator="$root/scripts/validate-static-analysis-json.sh"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

pass() {
  local mode="$1" input="$2" expected="$3"
  : > "$tmp/out"
  bash "$validator" "$mode" "$input" "$tmp/out"
  grep -Fqx "$expected" "$tmp/out"
}
reject() {
  local mode="$1" input="$2"
  : > "$tmp/out"
  if bash "$validator" "$mode" "$input" "$tmp/out" >"$tmp/stdout" 2>"$tmp/stderr"; then
    echo "FAIL: accepted unsafe $mode report: $input" >&2
    exit 1
  fi
  grep -Fq 'output rejected' "$tmp/stderr"
  [[ ! -s "$tmp/out" ]]
}

cat > "$tmp/hypatia.json" <<'JSON'
[
  {"severity":"critical","file":"src/a.rs","reason":"unsafe input"},
  {"severity":"high","file":"src/b.rs","type":"tainted source"},
  {"severity":"informational","file":"docs/a.adoc","message":"note"}
]
JSON
pass hypatia "$tmp/hypatia.json" 'critical=1'
grep -Fqx 'total=3' "$tmp/out"
grep -Fqx 'high=1' "$tmp/out"
grep -Fqx 'informational=1' "$tmp/out"

cat > "$tmp/empty.json" <<'JSON'
[]
JSON
pass hypatia "$tmp/empty.json" 'total=0'

printf '[]\n[]\n' > "$tmp/multiple.json"
reject hypatia "$tmp/multiple.json"
grep -Fq 'invalid JSON' "$tmp/stderr"
printf ' \n\t' > "$tmp/whitespace.json"
reject hypatia "$tmp/whitespace.json"
grep -Fq 'invalid JSON' "$tmp/stderr"

cat > "$tmp/missing-severity.json" <<'JSON'
[{"file":"src/a.rs","reason":"unknown severity must not vanish"}]
JSON
reject hypatia "$tmp/missing-severity.json"
cat > "$tmp/unknown-severity.json" <<'JSON'
[{"severity":"blocker","file":"src/a.rs","reason":"unrecognized"}]
JSON
reject hypatia "$tmp/unknown-severity.json"
cat > "$tmp/no-location.json" <<'JSON'
[{"severity":"critical","reason":"location missing"}]
JSON
reject hypatia "$tmp/no-location.json"
cat > "$tmp/non-array.json" <<'JSON'
{"severity":"critical"}
JSON
reject hypatia "$tmp/non-array.json"
cat > "$tmp/invalid.json" <<'JSON'
{"truncated":
JSON
reject hypatia "$tmp/invalid.json"

cat > "$tmp/assail.json" <<'JSON'
{"schema_version":"2.6","coverage":{"status":"complete","candidate_files":10,"analyzed_files":10},"weak_points":[{"severity":"Critical","description":"unsafe path","file":"src/a.rs","suppressed":false},{"severity":"High","description":"suppressed finding","file":"src/b.rs","suppressed":true}]}
JSON
pass assail "$tmp/assail.json" 'critical=1'
grep -Fqx 'total=1' "$tmp/out"

cat > "$tmp/assail-incomplete.json" <<'JSON'
{"schema_version":"2.6","coverage":{"status":"partial","candidate_files":10,"analyzed_files":1},"weak_points":[]}
JSON
reject assail "$tmp/assail-incomplete.json"
for change in '.coverage.candidate_files = 10.5' '.coverage.analyzed_files = 1.5' '.coverage.analyzed_files = 0'; do
  jq "$change" "$tmp/assail.json" > "$tmp/assail-invalid-coverage.json"
  reject assail "$tmp/assail-invalid-coverage.json"
done
cat > "$tmp/assail-old-schema.json" <<'JSON'
{"schema_version":"2.5","coverage":{"status":"complete","candidate_files":1,"analyzed_files":1},"weak_points":[]}
JSON
reject assail "$tmp/assail-old-schema.json"
cat > "$tmp/assail-unknown-severity.json" <<'JSON'
{"schema_version":"2.6","coverage":{"status":"complete","candidate_files":1,"analyzed_files":1},"weak_points":[{"severity":"Blocker","description":"unknown"}]}
JSON
reject assail "$tmp/assail-unknown-severity.json"

cat > "$tmp/bridge.json" <<'JSON'
{"schema_version":"0.3.0","vulnerability_data":"queried","cves":[{"classification":"mitigable"},{"classification":"unmitigable"},{"classification":"unmitigable"},{"classification":"informational"}],"mitigated":1,"unmitigable":2,"concatenative":0,"informational":1}
JSON
pass bridge "$tmp/bridge.json" 'unmitigable=2'
grep -Fqx 'bridge_status=completed' "$tmp/out"
for change in '.schema_version = "0.4.0"' '.cves = []' '.mitigated = 0' '.unmitigable = 0' '.informational = 0'; do
  jq "$change" "$tmp/bridge.json" > "$tmp/bridge-invalid.json"
  reject bridge "$tmp/bridge-invalid.json"
done

cat > "$tmp/bridge-no-dependencies.json" <<'JSON'
{"schema_version":"0.3.0","vulnerability_data":"no-dependencies","cves":[],"mitigated":0,"unmitigable":0,"concatenative":0,"informational":0}
JSON
pass bridge "$tmp/bridge-no-dependencies.json" 'bridge_status=completed'
cat > "$tmp/bridge-offline.json" <<'JSON'
{"schema_version":"0.3.0","vulnerability_data":"offline-unavailable","cves":[],"mitigated":0,"unmitigable":0,"concatenative":0,"informational":0}
JSON
reject bridge "$tmp/bridge-offline.json"
cat > "$tmp/bridge-missing.json" <<'JSON'
{"schema_version":"0.3.0","vulnerability_data":"Queried","cves":[],"mitigated":1,"unmitigable":0,"concatenative":0}
JSON
reject bridge "$tmp/bridge-missing.json"
cat > "$tmp/bridge-na.json" <<'JSON'
{"status":"not_applicable","reason":"no supported dependency lockfile is present"}
JSON
pass bridge "$tmp/bridge-na.json" 'bridge_status=not_applicable'

echo 'static-analysis JSON contract tests passed'
