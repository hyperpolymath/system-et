#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Validate the Cerro Torre manifest using a sample numeric template port.
# Usage: validate-stapeln-manifest.sh <manifest.toml>
set -euo pipefail

path="${1:?usage: $0 <manifest.toml>}"
[ -r "$path" ] || { echo "$path: cannot read manifest" >&2; exit 1; }

# Render the template placeholder with a sample port, then pull the
# listen_tcp key out of the [security.network] table.
line=$(sed 's/{{PORT}}/8080/g' "$path" | awk '
  /^[[:space:]]*\[/ { in_net = ($0 ~ /^[[:space:]]*\[security\.network\][[:space:]]*(#.*)?$/) ; next }
  in_net && /^[[:space:]]*listen_tcp[[:space:]]*=/ { print; exit }
')

if [ -z "$line" ]; then
  echo "$path: security.network.listen_tcp is missing" >&2
  exit 1
fi

if ! printf '%s\n' "$line" | grep -Eq '^[[:space:]]*listen_tcp[[:space:]]*=[[:space:]]*\[[[:space:]]*([0-9]+([[:space:]]*,[[:space:]]*[0-9]+)*)?[[:space:]]*,?[[:space:]]*\][[:space:]]*(#.*)?$'; then
  echo "$path: security.network.listen_tcp must be an array of integers" >&2
  exit 1
fi
