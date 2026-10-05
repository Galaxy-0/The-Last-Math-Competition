#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build
lake env lean -DwarningAsError=true Counterexample.lean
lake env lean -DwarningAsError=true Audit.lean
