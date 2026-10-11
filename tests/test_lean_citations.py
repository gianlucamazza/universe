"""Every fully qualified Lean name cited by Python or the docs must exist."""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CITED = re.compile(r"Universe\.([A-Z][A-Za-z]+)\.([A-Za-z_0-9]+)")
DECL = re.compile(
    r"^(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_0-9.']+)",
    re.MULTILINE,
)


def _sources() -> list[Path]:
    return [
        *ROOT.glob("universe/**/*.py"),
        ROOT / "README.md",
        *ROOT.glob("papers/*.md"),
    ]


def _declared(module: str) -> set[str]:
    path = ROOT / "Universe" / f"{module}.lean"
    if not path.exists():
        return set()
    return set(DECL.findall(path.read_text()))


def test_cited_lean_names_exist():
    missing = []
    for source in _sources():
        for module, name in CITED.findall(source.read_text()):
            if name not in _declared(module):
                missing.append(f"{source.relative_to(ROOT)}: Universe.{module}.{name}")
    assert not missing, "\n".join(sorted(set(missing)))
