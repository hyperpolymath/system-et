#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Validate scanner output before any severity count can influence a gate.
# Usage: validate-static-analysis-json.sh hypatia|assail|bridge FILE [GITHUB_OUTPUT]
set -euo pipefail

mode="${1:-}"
file="${2:-}"
output="${3:-${GITHUB_OUTPUT:-}}"

fail() {
  echo "::error::static-analysis output rejected: $*" >&2
  exit 1
}

case "$mode" in hypatia|assail|bridge) ;; *) fail "unknown report mode: $mode" ;; esac
[[ -n "$file" && -s "$file" ]] || fail "missing or empty report: ${file:-<unset>}"
command -v jq >/dev/null 2>&1 || fail "jq is required; no report was evaluated"
jq -e . "$file" >/dev/null 2>&1 || fail "invalid JSON in $file"
[[ -n "$output" ]] || fail "GITHUB_OUTPUT is not set"

write_findings_counts() {
  local total critical high medium low informational
  total="$(jq 'length' "$file")"
  critical="$(jq '[.[] | select(.severity == "critical" or .severity == "Critical") ] | length' "$file")"
  high="$(jq '[.[] | select(.severity == "high" or .severity == "High") ] | length' "$file")"
  medium="$(jq '[.[] | select(.severity == "medium" or .severity == "Medium") ] | length' "$file")"
  low="$(jq '[.[] | select(.severity == "low" or .severity == "Low") ] | length' "$file")"
  informational="$(jq '[.[] | select(.severity == "info" or .severity == "informational") ] | length' "$file")"
  {
    printf 'total=%s\n' "$total"
    printf 'critical=%s\n' "$critical"
    printf 'high=%s\n' "$high"
    printf 'medium=%s\n' "$medium"
    printf 'low=%s\n' "$low"
    printf 'informational=%s\n' "$informational"
  } >> "$output"
}

case "$mode" in
  hypatia)
    # Hypatia's documented JSON contract is an array of findings. Unknown or
    # absent severities are rejected instead of vanishing from a jq select().
    jq -e '
      type == "array" and
      all(.[];
        type == "object" and
        (.severity | type == "string" and
         IN("critical", "high", "medium", "low", "info", "informational")) and
        (.file | type == "string") and
        ((.reason? // .message? // .type?) | type == "string" and length > 0)
      )
    ' "$file" >/dev/null || fail "expected Hypatia array of findings with recognized severity, file, and description"
    write_findings_counts
    ;;
  assail)
    # The pinned panic-attack 2.6 report is an AssailReport object, not an array.
    # Require the exact schema generation and complete coverage; otherwise a
    # tool/schema upgrade or partial scan cannot be mistaken for zero findings.
    jq -e '
      type == "object" and .schema_version == "2.6" and
      (.coverage | type == "object" and .status == "complete" and
       (.candidate_files | type == "number" and . >= 0) and
       (.analyzed_files | type == "number" and . >= 0)) and
      (.weak_points | type == "array") and
      all(.weak_points[];
        type == "object" and
        (.severity | type == "string" and IN("Critical", "High", "Medium", "Low")) and
        (.description | type == "string" and length > 0) and
        ((.file? == null) or (.file | type == "string" and length > 0)) and
        ((.location? == null) or (.location | type == "string" and length > 0)) and
        ((.suppressed? == null) or (.suppressed | type == "boolean"))
      )
    ' "$file" >/dev/null || fail "expected complete panic-attack AssailReport schema 2.6"
    # Suppressed findings remain in the report for review but do not contribute
    # to scanner blocking counts, per the pinned tool's documented contract.
    jq '[.weak_points[] | select(.suppressed != true)]' "$file" > "${file}.active"
    file="${file}.active"
    write_findings_counts
    rm -f "${file}"
    ;;
  bridge)
    # The Patch Bridge contract distinguishes a real no-dependency scan from an
    # offline/unknown result. The latter is never a clean report.
    if jq -e 'type == "object" and .status == "not_applicable" and (.reason | type == "string" and length > 0)' "$file" >/dev/null; then
      printf 'bridge_status=not_applicable\n' >> "$output"
    else
      jq -e '
        type == "object" and
        (.schema_version | type == "string" and length > 0) and
        (.vulnerability_data | IN("queried", "no-dependencies")) and
        (.cves | type == "array") and
        ([.mitigated, .unmitigable, .concatenative, .informational] |
          all(.[]; type == "number" and . >= 0 and floor == .))
      ' "$file" >/dev/null || fail "expected online or confirmed no-dependencies Patch Bridge report"
      printf 'bridge_status=completed\n' >> "$output"
      {
        jq -r '"unmitigable=" + (.unmitigable|tostring)' "$file"
        jq -r '"mitigated=" + (.mitigated|tostring)' "$file"
        jq -r '"concatenative=" + (.concatenative|tostring)' "$file"
        jq -r '"informational=" + (.informational|tostring)' "$file"
      } >> "$output"
    fi
    ;;
esac
