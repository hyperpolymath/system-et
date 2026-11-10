#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# extract-facts.sh — the DESCRIPTIVE-side atomiser for Coaptation.
#
# Step 1 of the build path (descriptile half): give each descriptile a fact-list
# with STABLE IDs. Reads this repo's descriptive a2ml (the "descriptiles" family:
# CLADE/STATE/ECOSYSTEM/AGENTIC + anchors/ANCHOR) and projects the fields that can
# bear witness to contractile obligations into one deterministic JSON document.
#
# The scalar/arr/sh helpers are the same ones proven in arrival-pack/extract.sh.
# READER only — authors nothing; the a2ml files remain the single source of truth.
#
# Output (stdout): { "facts": [ {id,family,key,value,present} ... ],
#                   "provenance": { <family>: <hash> } }
set -euo pipefail

DIR6A2="${1:-.machine_readable/descriptiles}"
CLADE="$DIR6A2/CLADE.a2ml"
ECO="$DIR6A2/ECOSYSTEM.a2ml"
AGENTIC="$DIR6A2/AGENTIC.a2ml"
ANCHOR="$DIR6A2/anchors/ANCHOR.a2ml"

for f in "$CLADE" "$ECO" "$AGENTIC" "$ANCHOR"; do
  [ -f "$f" ] || { echo "extract-facts.sh: missing required a2ml: $f" >&2; exit 2; }
done

# scalar KEY FILE -> first `KEY = "value"` or unquoted `KEY = value` (anchored)
scalar() {
  local v
  v="$(grep -oP "^$1 = \"\K[^\"]+" "$2" | head -1 || true)"
  if [ -z "$v" ]; then
    v="$(grep -oP "^$1 = \K[^\"#]+" "$2" | head -1 | sed 's/[[:space:]]*$//' || true)"
  fi
  printf '%s' "$v"
}

# STATE v1 is archived (state-v1-decision, option B). Its live successors: the repo deed
# carries the lifecycle (status) and maturity clauses; the thin journal carries the phase.
DEED="$DIR6A2/../../$(scalar 'canonical-name' "$CLADE")_chora.deed"
JOURNAL="$DIR6A2/../../docs/status/JOURNAL.adoc"
for f in "$DEED" "$JOURNAL"; do
  [[ -f "$f" ]] || { echo "extract-facts.sh: missing required file: $f" >&2; exit 2; }
done

# deed_sym CLAUSE KEYWORD -> the symbol after `(CLAUSE ... :KEYWORD ` on the clause's opening line
deed_sym() {
  local clause="$1" keyword="$2"
  grep -oP "^\s*\($clause\s+:$keyword\s+\K[A-Za-z0-9_-]+" "$DEED" | head -1 || true
}

# journal_phase -> the first word of the journal's `phase::` value (the phase label)
journal_phase() {
  awk '/^phase::$/{getline; split($0,a,/[ .:]/); print a[1]; exit}' "$JOURNAL"
}

# arr KEY FILE SEP -> join all quoted strings in the `KEY = [ ... ]` block
arr() {
  local key="$1" file="$2" sep="${3:-, }" out="" i
  local -a items
  mapfile -t items < <(
    awk -v k="$key" '
      index($0, k" = [")==1 {grab=1}
      grab {print}
      grab && /\]/ {exit}
    ' "$file" | grep -oP '"[^"]*"' | sed 's/^"//; s/"$//' || true
  )
  for i in "${!items[@]}"; do
    if [ "$i" -eq 0 ]; then out="${items[$i]}"; else out="$out$sep${items[$i]}"; fi
  done
  printf '%s' "$out"
}

# short content hash (drift provenance)
sh() { sha256sum "$1" | cut -c1-12; }

# id <TAB> value rows. Empty value => present:false in jq below.
emit() { printf '%s\t%s\n' "$1" "$2"; }

rows="$(
  # --- CLADE: identity / lineage ---
  emit 'clade.uuid'             "$(scalar 'uuid' "$CLADE")"
  emit 'clade.canonical-name'   "$(scalar 'canonical-name' "$CLADE")"
  emit 'clade.prefixed-name'    "$(scalar 'prefixed-name' "$CLADE")"
  emit 'clade.primary'          "$(scalar 'primary' "$CLADE")"
  emit 'clade.born'             "$(scalar 'born' "$CLADE")"
  emit 'clade.forge-github'     "$(scalar 'github' "$CLADE")"
  # --- STATE: where things are now (deed + journal; STATE v1 is archived) ---
  emit 'state.status'                 "$(deed_sym status phase)"
  emit 'state.phase'                  "$(journal_phase)"
  emit 'state.maturity'               "$(deed_sym maturity level)"
  # No source exists for these since STATE v1 was archived: completion is derivable,
  # and the other three mirrored a maintenance report that never ran. They are emitted
  # EMPTY so they register as ABSENT (present:false), never as a recorded zero.
  emit 'state.completion-percentage'  ""
  emit 'state.open-warnings'          ""
  emit 'state.open-failures'          ""
  emit 'state.last-result'            ""
  # --- ECOSYSTEM: where it sits + IS-NOT boundary ---
  emit 'ecosystem.type'             "$(scalar 'type' "$ECO")"
  emit 'ecosystem.position'         "$(scalar 'position' "$ECO")"
  emit 'ecosystem.coordination'     "$(scalar 'coordination' "$ECO")"
  emit 'ecosystem.what-this-is-not' "$(arr 'what-this-is-not' "$ECO" ' · ')"
  # --- AGENTIC: may I act / integrity posture ---
  emit 'agentic.fail-closed'                       "$(scalar 'fail-closed' "$AGENTIC")"
  emit 'agentic.allow-silent-skip'                 "$(scalar 'allow-silent-skip' "$AGENTIC")"
  emit 'agentic.require-evidence-per-step'         "$(scalar 'require-evidence-per-step' "$AGENTIC")"
  emit 'agentic.release-claim-requires-hard-pass'  "$(scalar 'release-claim-requires-hard-pass' "$AGENTIC")"
  emit 'agentic.default-mode'                      "$(scalar 'default-mode' "$AGENTIC")"
  # --- ANCHOR: semantic authority + golden path ---
  emit 'anchor.authority'            "$(scalar 'authority' "$ANCHOR")"
  emit 'anchor.policy'               "$(scalar 'policy' "$ANCHOR")"
  emit 'anchor.project'              "$(scalar 'project' "$ANCHOR")"
  emit 'anchor.golden-path'          "$(arr 'smoke-test-command' "$ANCHOR" ' && ')"
  emit 'anchor.success-criteria'     "$(arr 'success-criteria' "$ANCHOR" '; ')"
  emit 'anchor.must-have-anchor'     "$(scalar 'must-have-anchor' "$ANCHOR")"
  emit 'anchor.must-have-golden-path' "$(scalar 'must-have-golden-path' "$ANCHOR")"
)"

printf '%s\n' "$rows" | jq -R -s \
  --arg clade     "$(sh "$CLADE")" \
  --arg deed      "$(sh "$DEED")" \
  --arg ecosystem "$(sh "$ECO")" \
  --arg agentic   "$(sh "$AGENTIC")" \
  --arg anchor    "$(sh "$ANCHOR")" \
  '
  {
    facts: (
      split("\n") | map(select(length > 0)) | map(split("\t")) | map({
        id:      .[0],
        family:  (.[0] | split(".")[0]),
        key:     (.[0] | split(".") | .[1:] | join(".")),
        value:   (.[1] // ""),
        present: ((.[1] // "") | length > 0)
      })
    ),
    provenance: {
      clade: $clade, deed: $deed, ecosystem: $ecosystem,
      agentic: $agentic, anchor: $anchor
    }
  }
'
