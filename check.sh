#!/usr/bin/env bash
# Run every gate: lint, format, unit tests, the Python certificate, the Lean build.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

ruff check .
ruff format --check .
python -m pytest -q tests
python -m universe >/dev/null
lake build
echo "ok"
