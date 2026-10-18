#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker Conjecture3944
lake env leanchecker Audit
python3 independent.py
printf 'All verification commands passed.\n'
