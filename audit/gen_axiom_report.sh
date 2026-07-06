#!/usr/bin/env bash
# Verification axis (formalization-assurance): regenerate / check the golden `#print axioms` trace.
#   bash audit/gen_axiom_report.sh           # regenerate audit/axiom-report.txt
#   bash audit/gen_axiom_report.sh --check    # fail if the live trace drifts from the golden file
set -euo pipefail
cd "$(dirname "$0")/.."
live="$(lake env lean audit/axiom_report.lean 2>/dev/null)"
if [[ "${1:-}" == "--check" ]]; then
  if diff <(printf '%s\n' "$live") audit/axiom-report.txt; then
    echo "✓ axiom report in sync"
  else
    echo "✗ AXIOM REPORT DRIFT — regenerate: bash audit/gen_axiom_report.sh" >&2; exit 1
  fi
else
  printf '%s\n' "$live" > audit/axiom-report.txt; echo "wrote audit/axiom-report.txt"
fi
