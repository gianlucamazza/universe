"""Every count of certificate lines written in the docs matches the certificate."""

import re
from pathlib import Path

from universe.proofs import prove

ROOT = Path(__file__).resolve().parent.parent
PATTERNS = (
    re.compile(r"prints (\d+) lines"),
    re.compile(r"one of the (\d+)\b"),
    re.compile(r"stampa (\d+) (?:righe|identità)"),
    re.compile(r"stampa `(\d+)/(\d+)`"),
)


def _docs() -> list[Path]:
    return [
        ROOT / "README.md",
        *ROOT.glob("papers/*.md"),
        *ROOT.glob("researches/*.md"),
    ]


def test_doc_counts_match_certificate():
    total = len(prove())
    wrong = []
    for doc in _docs():
        text = doc.read_text()
        for pattern in PATTERNS:
            for match in pattern.finditer(text):
                if any(int(n) != total for n in match.groups()):
                    wrong.append(
                        f"{doc.relative_to(ROOT)}: '{match.group(0)}' != {total}"
                    )
    assert not wrong, "\n".join(wrong)
