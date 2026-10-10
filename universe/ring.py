"""Scalari esatti: razionali di Gauss e quoziente polinomiale.

Ogni regola `name² = sostituto` dichiarata con `Ring.set_square` è un
generatore. `reduce_witness` sbuccia quelle regole, in ordine di indice, e
restituisce resto e cofattori. Nell'anello libero
`p = resto + Σ fᵢ·(xᵢ² − sostitutoᵢ)`.
Se il resto ha tutti i coefficienti zero, questa espansione esibisce
l'appartenenza all'ideale generato da quelle regole.
Il converso, per `Universe.Quotient.reduce`, è `Universe.Dynamics.reduce_complete`:
non è un teorema su questo riduttore.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True, order=True)
class Gauss:
    """Numero a + b i con a, b razionali."""

    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)

    def __add__(self, other: Gauss) -> Gauss:
        return Gauss(self.re + other.re, self.im + other.im)

    def __sub__(self, other: Gauss) -> Gauss:
        return Gauss(self.re - other.re, self.im - other.im)

    def __neg__(self) -> Gauss:
        return Gauss(-self.re, -self.im)

    def __mul__(self, other: Gauss) -> Gauss:
        return Gauss(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def __pow__(self, n: int) -> Gauss:
        if n < 0:
            raise ValueError("potenza negativa")
        result = Gauss(Fraction(1), Fraction(0))
        base = self
        while n:
            if n & 1:
                result *= base
            n >>= 1
            if n:
                base *= base
        return result

    def conj(self) -> Gauss:
        return Gauss(self.re, -self.im)

    def is_zero(self) -> bool:
        return self.re == 0 and self.im == 0


def g(real: int | Fraction = 0, imag: int | Fraction = 0) -> Gauss:
    return Gauss(Fraction(real), Fraction(imag))


ZERO_G = g(0)
ONE_G = g(1)


class Ring:
    """Anello di polinomi sui razionali di Gauss, con quadrati riscrivibili."""

    def __init__(self, variables: tuple[str, ...]):
        if len(set(variables)) != len(variables):
            raise ValueError("variabile duplicata")
        self.variables = variables
        self._index = {name: i for i, name in enumerate(variables)}
        # Indice di variabile il cui quadrato si riscrive, in ordine di peeling.
        self.squares: dict[int, Poly] = {}

    def __repr__(self) -> str:
        return f"Ring{self.variables}"

    def index(self, name: str) -> int:
        return self._index[name]

    def zero(self) -> Poly:
        return _from_origin(Raw.zero(self))

    def one(self) -> Poly:
        return self.constant(ONE_G)

    def constant(self, value: Gauss) -> Poly:
        if value.is_zero():
            return self.zero()
        return _from_origin(_mono(self, value))

    def var(self, name: str) -> Poly:
        return _from_origin(_mono(self, **{name: 1}))

    def set_square(self, name: str, replacement: Poly) -> None:
        """Dichiara name² = replacement. Il peeling legge questa regola."""
        if replacement.ring is not self:
            raise ValueError("anelli diversi")
        idx = self.index(name)
        normal = replacement.reduced()
        for exp, _coeff in normal.terms:
            if exp[idx] != 0:
                raise ValueError(f"il sostituto di {name}² contiene ancora {name}")
        self.squares[idx] = normal


def _canon(
    items: dict[tuple[int, ...], Gauss],
) -> tuple[tuple[tuple[int, ...], Gauss], ...]:
    cleaned = [(exp, coeff) for exp, coeff in items.items() if not coeff.is_zero()]
    cleaned.sort(key=lambda ec: (sum(ec[0]), ec[0]))
    return tuple(cleaned)


@dataclass(frozen=True)
class Raw:
    """Polinomio libero. I quadrati non si riscrivono."""

    ring: Ring
    terms: tuple[tuple[tuple[int, ...], Gauss], ...]

    @staticmethod
    def zero(ring: Ring) -> Raw:
        return Raw(ring, ())

    def is_zero(self) -> bool:
        return not self.terms

    def eq(self, other: Raw) -> bool:
        if self.ring is not other.ring:
            raise ValueError("anelli diversi")
        return self.terms == other.terms

    def __add__(self, other: Raw) -> Raw:
        self._same(other)
        acc = dict(self.terms)
        for exp, coeff in other.terms:
            acc[exp] = acc.get(exp, ZERO_G) + coeff
        return Raw(self.ring, _canon(acc))

    def __neg__(self) -> Raw:
        return Raw(self.ring, tuple((exp, -coeff) for exp, coeff in self.terms))

    def __sub__(self, other: Raw) -> Raw:
        return self + (-other)

    def scale(self, factor: Gauss) -> Raw:
        if factor.is_zero():
            return Raw.zero(self.ring)
        acc = {exp: coeff * factor for exp, coeff in self.terms}
        return Raw(self.ring, _canon(acc))

    def __mul__(self, other: Raw) -> Raw:
        self._same(other)
        acc: dict[tuple[int, ...], Gauss] = {}
        width = len(self.ring.variables)
        for e1, c1 in self.terms:
            for e2, c2 in other.terms:
                exp = tuple(e1[i] + e2[i] for i in range(width))
                acc[exp] = acc.get(exp, ZERO_G) + c1 * c2
        return Raw(self.ring, _canon(acc))

    def conj(self) -> Raw:
        acc = {exp: coeff.conj() for exp, coeff in self.terms}
        return Raw(self.ring, _canon(acc))

    def real_imag(self) -> tuple[Raw, Raw]:
        re: dict[tuple[int, ...], Gauss] = {}
        im: dict[tuple[int, ...], Gauss] = {}
        for exp, coeff in self.terms:
            if coeff.re != 0:
                re[exp] = g(coeff.re)
            if coeff.im != 0:
                im[exp] = g(coeff.im)
        return Raw(self.ring, _canon(re)), Raw(self.ring, _canon(im))

    def _same(self, other: Raw) -> None:
        if self.ring is not other.ring:
            raise ValueError("anelli diversi")


def _mono(ring: Ring, coeff: Gauss = ONE_G, **powers: int) -> Raw:
    if coeff.is_zero():
        return Raw.zero(ring)
    exp = [0] * len(ring.variables)
    for name, power in powers.items():
        exp[ring.index(name)] = power
    return Raw(ring, ((tuple(exp), coeff),))


def _rules(
    ring: Ring, extra: tuple[tuple[int, Raw], ...] = ()
) -> tuple[tuple[int, Raw], ...]:
    declared = tuple(
        (idx, Raw(ring, ring.squares[idx].terms)) for idx in sorted(ring.squares)
    )
    return declared + extra


def _square_generator(ring: Ring, index: int, replacement: Raw) -> Raw:
    """`x² − sostituto`, il generatore della regola."""
    exp = [0] * len(ring.variables)
    exp[index] = 2
    return Raw(ring, ((tuple(exp), ONE_G),)) - replacement


def _has_square(raw: Raw, index: int) -> bool:
    return any(exp[index] >= 2 for exp, _coeff in raw.terms)


def _peel_rule(raw: Raw, index: int, replacement: Raw) -> tuple[Raw, Raw]:
    """Un passo: `x² = sostituto + (x² − sostituto)`."""
    width = len(raw.ring.variables)
    kept: dict[tuple[int, ...], Gauss] = {}
    cofactor: dict[tuple[int, ...], Gauss] = {}
    for exp, coeff in raw.terms:
        if exp[index] < 2:
            kept[exp] = kept.get(exp, ZERO_G) + coeff
            continue
        base = list(exp)
        base[index] -= 2
        base_key = tuple(base)
        cofactor[base_key] = cofactor.get(base_key, ZERO_G) + coeff
        for rexp, rcoeff in replacement.terms:
            merged = tuple(base[i] + rexp[i] for i in range(width))
            kept[merged] = kept.get(merged, ZERO_G) + coeff * rcoeff
    return Raw(raw.ring, _canon(kept)), Raw(raw.ring, _canon(cofactor))


def reduce_witness(
    raw: Raw, extra: tuple[tuple[int, Raw], ...] = ()
) -> tuple[Raw, tuple[Raw, ...]]:
    """Resto e un cofattore per regola. Le regole extra seguono quelle dell'anello."""
    current = raw
    factors: list[Raw] = []
    for index, replacement in _rules(raw.ring, extra):
        factor = Raw.zero(raw.ring)
        steps = 0
        while _has_square(current, index):
            current, step = _peel_rule(current, index, replacement)
            factor = factor + step
            steps += 1
            if steps > 10000:
                raise RuntimeError(f"riduzione della variabile {index}")
        factors.append(factor)
    return current, tuple(factors)


def witness_holds(
    origin: Raw,
    remainder: Raw,
    factors: tuple[Raw, ...],
    extra: tuple[tuple[int, Raw], ...] = (),
) -> bool:
    rules = _rules(origin.ring, extra)
    if len(factors) != len(rules):
        return False
    rebuilt = remainder
    for (index, replacement), factor in zip(rules, factors, strict=True):
        rebuilt = rebuilt + factor * _square_generator(origin.ring, index, replacement)
    return rebuilt.eq(origin)


def _from_origin(origin: Raw) -> Poly:
    remainder, _factors = reduce_witness(origin)
    return Poly(origin.ring, remainder.terms, origin)


@dataclass(frozen=True)
class Poly:
    ring: Ring
    terms: tuple[tuple[tuple[int, ...], Gauss], ...]
    origin: Raw

    def __repr__(self) -> str:
        return str(self)

    def is_zero(self) -> bool:
        return not self.terms

    def is_one(self) -> bool:
        return self == self.ring.one()

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Poly):
            return NotImplemented
        if self.ring is not other.ring:
            raise ValueError("confronto fra anelli diversi")
        return self.terms == other.terms

    def __add__(self, other: Poly) -> Poly:
        self._same(other)
        return _from_origin(self.origin + other.origin)

    def __sub__(self, other: Poly) -> Poly:
        return self + (-other)

    def __neg__(self) -> Poly:
        return _from_origin(-self.origin)

    def __mul__(self, other: Gauss | Poly) -> Poly:
        if isinstance(other, Gauss):
            return _from_origin(self.origin.scale(other))
        if not isinstance(other, Poly):
            return NotImplemented
        self._same(other)
        return _from_origin(self.origin * other.origin)

    def __rmul__(self, other: Gauss) -> Poly:
        return self * other

    def __pow__(self, n: int) -> Poly:
        if n < 0:
            raise ValueError("potenza negativa")
        result = self.ring.one()
        if n == 0:
            return result
        base = self
        while n:
            if n & 1:
                result *= base
            n >>= 1
            if n:
                base *= base
        return result

    def conj(self) -> Poly:
        return _from_origin(self.origin.conj())

    def modulus_squared(self) -> Poly:
        return self * self.conj()

    def reduced(self) -> Poly:
        return _from_origin(self.origin)

    def witness(self) -> tuple[bool, bool]:
        """`(cofattori_ok, resto_zero)`.

        `cofattori_ok` è l'uguaglianza libera
        `origine = resto + Σ fᵢ·(xᵢ² − sostitutoᵢ)`.
        """
        remainder, factors = reduce_witness(self.origin)
        cofactors = remainder.terms == self.terms and witness_holds(
            self.origin, remainder, factors
        )
        return cofactors, remainder.is_zero()

    def certification(self) -> str | None:
        """`None` se il resto è zero e l'espansione libera dei cofattori ridà l'origine."""
        cofactors, is_zero = self.witness()
        if not cofactors:
            return "cofattori non tornano"
        if not is_zero:
            return f"resto = {self}"
        return None

    def certify_extra(self, name: str, replacement: Poly) -> str | None:
        """`None` quando il resto è zero e i cofattori ricostruiscono l'origine.

        La regola extra è `name² − replacement`, accanto a quelle dell'anello.
        Il sostituto è la forma già ridotta. Il resto zero esibisce
        l'appartenenza all'ideale generato da quelle regole.
        """
        self._same(replacement)
        idx = self.ring.index(name)
        if idx in self.ring.squares:
            raise ValueError(f"{name}² è già una regola dell'anello")
        normal = replacement.reduced()
        for exp, _coeff in normal.terms:
            if exp[idx] != 0:
                raise ValueError(f"il sostituto di {name}² contiene ancora {name}")
        extra = ((idx, Raw(self.ring, normal.terms)),)
        remainder, factors = reduce_witness(self.origin, extra)
        if not witness_holds(self.origin, remainder, factors, extra):
            return "cofattori non tornano"
        if not remainder.is_zero():
            shown = Poly(self.ring, remainder.terms, remainder)
            return f"resto = {shown}"
        return None

    def substitute(self, values: dict[str, Gauss]) -> Poly:
        acc: dict[tuple[int, ...], Gauss] = {}
        for exp, coeff in self.terms:
            exponents = list(exp)
            term = coeff
            for name, value in values.items():
                idx = self.ring.index(name)
                power = exponents[idx]
                if power:
                    term *= value**power
                    exponents[idx] = 0
            if not term.is_zero():
                key = tuple(exponents)
                acc[key] = acc.get(key, ZERO_G) + term
        return _from_origin(Raw(self.ring, _canon(acc)))

    def evaluate(self, values: dict[str, Gauss]) -> Gauss:
        missing = [
            name
            for name, exp in zip(self.ring.variables, self._support(), strict=True)
            if exp and name not in values
        ]
        if missing:
            raise ValueError(f"variabili libere: {', '.join(missing)}")
        total = ZERO_G
        for exp, coeff in self.terms:
            term = coeff
            for name, power in zip(self.ring.variables, exp, strict=True):
                if power:
                    term *= values[name] ** power
            total += term
        return total

    def imag_is_zero(self) -> bool:
        return all(coeff.im == 0 for _exp, coeff in self.terms)

    def real_imag(self) -> tuple[Poly, Poly]:
        real, imag = self.origin.real_imag()
        return _from_origin(real), _from_origin(imag)

    def _support(self) -> tuple[int, ...]:
        if not self.terms:
            return (0,) * len(self.ring.variables)
        width = len(self.ring.variables)
        acc = [0] * width
        for exp, _coeff in self.terms:
            for i in range(width):
                acc[i] = max(acc[i], exp[i])
        return tuple(acc)

    def _same(self, other: Poly) -> None:
        if self.ring is not other.ring:
            raise ValueError("anelli diversi")

    def __str__(self) -> str:
        if not self.terms:
            return "0"
        chunks: list[str] = []
        for index, (exp, coeff) in enumerate(self.terms):
            piece = _piece(coeff, _monomial(self.ring, exp))
            if index == 0:
                chunks.append(piece)
            elif piece.startswith("-"):
                chunks.append(" - " + piece[1:])
            else:
                chunks.append(" + " + piece)
        return "".join(chunks)


def _monomial(ring: Ring, exp: tuple[int, ...]) -> str:
    parts: list[str] = []
    for name, power in zip(ring.variables, exp, strict=True):
        if power == 1:
            parts.append(name)
        elif power > 1:
            parts.append(f"{name}^{power}")
    return " ".join(parts)


def _piece(coeff: Gauss, mono: str) -> str:
    if coeff.im == 0:
        re = coeff.re
        if mono == "":
            return str(re)
        if re == 1:
            return mono
        if re == -1:
            return "-" + mono
        return f"{re} {mono}"
    if coeff.re == 0:
        im = coeff.im
        body = "i" if mono == "" else f"i {mono}"
        if im == 1:
            return body
        if im == -1:
            return "-" + body
        sign = "" if im > 0 else "-"
        return f"{sign}{abs(im)} {body}"
    sign = "+" if coeff.im > 0 else "-"
    imag = abs(coeff.im)
    imag_s = "i" if imag == 1 else f"{imag} i"
    body = f"({coeff.re}{sign}{imag_s})"
    return body if mono == "" else f"{body} {mono}"


@dataclass
class Scalars:
    """Linguaggio scalare del primo universo.

    c, s sono le indeterminate del quoziente c² + s² = 1.
    Nella forma chiusa si leggono come cos φ e sin φ, con φ = ω t / 2.
    n = (nx, ny, nz) è l'asse dell'Hamiltoniana, con nx² + ny² + nz² = 1.
    ar, ai, br, bi sono le parti reali e immaginarie di uno stato generico.
    """

    ring: Ring
    c: Poly
    s: Poly
    nx: Poly
    ny: Poly
    nz: Poly
    ar: Poly
    ai: Poly
    br: Poly
    bi: Poly

    @property
    def one(self) -> Poly:
        return self.ring.one()

    @property
    def zero(self) -> Poly:
        return self.ring.zero()


def qubit_scalars() -> Scalars:
    names = ("c", "s", "nx", "ny", "nz", "ar", "ai", "br", "bi")
    ring = Ring(names)
    symbol = {name: ring.var(name) for name in names}
    one = ring.one()
    # Orientamento della riscrittura: c prima di s, nx prima di ny e di nz.
    ring.set_square("c", one - symbol["s"] ** 2)
    ring.set_square("nx", one - symbol["ny"] ** 2 - symbol["nz"] ** 2)
    return Scalars(ring=ring, **symbol)
