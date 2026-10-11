"""Every certificate line is tied to Lean theorems that exist."""

import re
from pathlib import Path

from universe.lean_map import LEAN
from universe.proofs import prove

ROOT = Path(__file__).resolve().parent.parent
DECL = re.compile(
    r"^\s*(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_0-9.']+)",
    re.MULTILINE,
)


def _declared(module: str) -> set[str]:
    path = ROOT / "Universe" / f"{module}.lean"
    return set(DECL.findall(path.read_text())) if path.exists() else set()


def test_every_line_is_mapped():
    names = [theorem.name for theorem in prove()]
    assert sorted(LEAN) == sorted(names)
    assert all(LEAN[name] for name in names)


def test_every_lean_name_exists():
    missing = []
    for line, theorems in LEAN.items():
        for full in theorems:
            _, module, *rest = full.split(".")
            if rest[-1] not in _declared(module):
                missing.append(f"{line}: {full}")
    assert not missing, "\n".join(missing)
