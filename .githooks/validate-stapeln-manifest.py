# SPDX-License-Identifier: MPL-2.0
"""Validate the Cerro Torre manifest using a sample numeric template port."""

import sys
import tomllib
from pathlib import Path

path = Path(sys.argv[1])
try:
    manifest = tomllib.loads(path.read_text(encoding="utf-8").replace("{{PORT}}", "8080"))
    ports = manifest["security"]["network"]["listen_tcp"]
    if not isinstance(ports, list) or any(type(port) is not int for port in ports):
        raise ValueError("security.network.listen_tcp must be an array of integers")
except (OSError, KeyError, ValueError) as exc:
    sys.exit(f"{path}: {exc}")
