#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lean --version
lake --version
lake build
lake env lean -j1 scripts/Audit.lean
while IFS= read -r audit; do
  lake env lean -j1 "$audit"
done < <(find GraphicalAllocation -name Audit.lean -print | sort)
