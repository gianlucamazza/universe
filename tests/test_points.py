"""Lean and the certificate print the same rational points."""

from fractions import Fraction
from pathlib import Path

from universe.points import points

ROOT = Path(__file__).resolve().parent.parent


def _text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _fraction(token: str) -> Fraction:
    value = Fraction(token)
    assert token == _text(value)
    return value


def _parse(text: str) -> list[tuple[str, Fraction, Fraction]]:
    rows = []
    for line in text.splitlines():
        key, real, imag = line.split()
        rows.append((key, _fraction(real), _fraction(imag)))
    return rows


def test_points_file_matches_certificate():
    parsed = _parse((ROOT / "points.txt").read_text())
    table = points()
    assert [key for key, _, _ in parsed] == sorted(table)
    assert {(key, real, imag) for key, real, imag in parsed} == {
        (key, real, imag) for key, (real, imag) in table.items()
    }
