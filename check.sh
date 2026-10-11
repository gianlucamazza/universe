#!/usr/bin/env bash
# Run every gate: lint, format, unit tests, the Python certificate, the Lean build.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

# Same ruff as CI (pyproject dev extra); fall back to the system one.
if command -v uvx >/dev/null; then ruff=(uvx -q ruff@0.17.0); else ruff=(ruff); fi
"${ruff[@]}" check .
"${ruff[@]}" format --check .
# Markdown formatting, as in CI, when prettier is installed.
if command -v prettier >/dev/null; then prettier --check --log-level warn "**/*.md"; fi
python -m pytest -q tests
python -m universe >/dev/null
lake build --wfail
echo "ok"
