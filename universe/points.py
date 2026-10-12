"""Tabella dei punti razionali, dagli stessi conti del certificato.

Ogni chiave cita il teorema il cui membro sinistro è la voce Lean.
I valori sono quelli che `proofs.py` calcola già per le sue righe.
"""

from __future__ import annotations

from fractions import Fraction

from universe.angle import (
    addition_witness,
    angle_half_reading,
    circle_at_one,
    group_witness,
    remainder_witness,
)
from universe.proofs import (
    axes_point,
    bell_point,
    change_of_basis,
    cnot_sample,
    compose_point,
    corollary_cells,
    corollary_matrix,
    energy_point,
    friend_point,
    luders_point,
    modulus_gauss,
    partial_points,
)
from universe.ring import Gauss
from universe.worlds.qubit import QubitUniverse


def _pair(value: Gauss) -> tuple[Fraction, Fraction]:
    return value.re, value.im


def _real(value: Fraction) -> tuple[Fraction, Fraction]:
    return value, Fraction(0)


def points(world: QubitUniverse | None = None) -> dict[str, tuple[Fraction, Fraction]]:
    """`chiave → (re, im)`, dagli stessi valori del certificato."""
    world = world or QubitUniverse()
    matrix = corollary_matrix(world)
    bell = bell_point(world)
    friend = friend_point(world)
    idle, mid, flip = partial_points(world)
    luders = luders_point(world)
    change = change_of_basis(world)
    axes = axes_point()
    cells, _cells_right = corollary_cells(world)
    before_x, after_x, before_z, after_z = energy_point(world)
    sample, sample_weights = cnot_sample(world)
    composed = compose_point()
    cosine, sine, gap, bound = circle_at_one()
    group_cos, group_sin, group_bound = group_witness()
    rest, cap = remainder_witness()
    (
        half_c,
        half_s,
        half_0,
        half_1,
        half_p0,
        half_p1,
        half_gap,
        half_rem,
    ) = angle_half_reading()
    add_cos, add_sin = addition_witness()
    # Universe.Epistemology.point_prob0
    weight0 = modulus_gauss(matrix[0][0])
    # Universe.Epistemology.point_prob1
    weight1 = modulus_gauss(matrix[1][0])
    return {
        # Universe.Symmetry.point_axes
        "axes.a": _pair(axes.amplitude),
        # Universe.Symmetry.point_axes
        "axes.bx": _pair(axes.vector[0]),
        # Universe.Symmetry.point_axes
        "axes.by": _pair(axes.vector[1]),
        # Universe.Symmetry.point_axes
        "axes.bz": _pair(axes.vector[2]),
        # Universe.Symmetry.rotations_noncommute
        "axes.mn.0": _pair(axes.backward[0]),
        # Universe.Symmetry.rotations_noncommute
        "axes.mn.1": _pair(axes.backward[1]),
        # Universe.Symmetry.rotations_noncommute
        "axes.mn.p0": _pair(axes.backward_weights[0]),
        # Universe.Symmetry.rotations_noncommute
        "axes.mn.p1": _pair(axes.backward_weights[1]),
        # Universe.Symmetry.point_axes
        "axes.nm.0": _pair(axes.forward[0]),
        # Universe.Symmetry.point_axes
        "axes.nm.1": _pair(axes.forward[1]),
        # Universe.Symmetry.rotations_noncommute
        "axes.nm.p0": _pair(axes.forward_weights[0]),
        # Universe.Symmetry.rotations_noncommute
        "axes.nm.p1": _pair(axes.forward_weights[1]),
        # Universe.Observer.point_bell
        "bell.00": _pair(bell.amplitudes[0]),
        # Universe.Observer.point_bell
        "bell.01": _pair(bell.amplitudes[1]),
        # Universe.Observer.point_bell
        "bell.10": _pair(bell.amplitudes[2]),
        # Universe.Observer.point_bell
        "bell.11": _pair(bell.amplitudes[3]),
        # Universe.Observer.point_cells
        "cell.0": _real(cells[0]),
        # Universe.Observer.point_cells
        "cell.1": _real(cells[1]),
        # Universe.Observer.point_cells
        "cell.2": _real(cells[2]),
        # Universe.Observer.point_cells
        "cell.3": _real(cells[3]),
        # Universe.Observer.point_cells
        "cell.4": _real(cells[4]),
        # Universe.Observer.point_cells
        "cell.5": _real(cells[5]),
        # Universe.Observer.point_cells
        "cell.6": _real(cells[6]),
        # Universe.Observer.point_cells
        "cell.7": _real(cells[7]),
        # Universe.Symmetry.point_compose
        "compose.0": _pair(composed.image[0]),
        # Universe.Symmetry.point_compose
        "compose.1": _pair(composed.image[1]),
        # Universe.Symmetry.point_compose
        "compose.c": _pair(composed.cosine),
        # Universe.Symmetry.point_compose
        "compose.s": _pair(composed.sine),
        # Universe.Observer.point_copied
        "copied.coh": _pair(friend.copied_coherence),
        # Universe.Observer.point_copied
        "copied.purity": _pair(friend.copied_purity),
        # Universe.Observer.point_copied
        "copied.w0": _pair(friend.weight0),
        # Universe.Observer.point_copied
        "copied.w1": _pair(friend.weight1),
        # Universe.Observer.point_entangled
        "det": _pair(bell.determinant),
        # Universe.Symmetry.point_energy_x
        "energy.x.after": _pair(after_x),
        # Universe.Symmetry.point_energy_x
        "energy.x.before": _pair(before_x),
        # Universe.Symmetry.point_energy_z
        "energy.z.after": _pair(after_z),
        # Universe.Symmetry.point_energy_z
        "energy.z.before": _pair(before_z),
        # Universe.Interaction.point_partial_flip
        "flip.coh": _pair(flip.coherence),
        # Universe.Interaction.point_partial_flip
        "flip.purity": _pair(flip.purity),
        # Universe.Interaction.point_partial_idle
        "idle.coh": _pair(idle.coherence),
        # Universe.Interaction.point_partial_idle
        "idle.purity": _pair(idle.purity),
        # Universe.Interaction.point_luders
        "luders.0.0": _pair(luders.read0[0]),
        # Universe.Interaction.point_luders
        "luders.0.1": _pair(luders.read0[1]),
        # Universe.Interaction.point_luders
        "luders.1.0": _pair(luders.read1[0]),
        # Universe.Interaction.point_luders
        "luders.1.1": _pair(luders.read1[1]),
        # Universe.Interaction.point_luders
        "luders.n0": _pair(luders.norm0),
        # Universe.Interaction.point_luders
        "luders.n1": _pair(luders.norm1),
        # Universe.Interaction.point_partial_mid
        "mid.coh": _pair(mid.coherence),
        # Universe.Interaction.point_partial_mid
        "mid.purity": _pair(mid.purity),
        # Universe.Epistemology.point_prob0
        "p0": _pair(weight0),
        # Universe.Epistemology.point_prob1
        "p1": _pair(weight1),
        # Universe.Observer.point_purity
        "purity": _pair(bell.purity),
        # Universe.Interaction.point_repeatable
        "repeat.0.0": _pair(luders.again0[0]),
        # Universe.Interaction.point_repeatable
        "repeat.0.1": _pair(luders.again0[1]),
        # Universe.Interaction.point_repeatable
        "repeat.1.0": _pair(luders.again1[0]),
        # Universe.Interaction.point_repeatable
        "repeat.1.1": _pair(luders.again1[1]),
        # Universe.Interaction.point_cnot_sample
        "sample.00": _pair(sample[0]),
        # Universe.Interaction.point_cnot_sample
        "sample.01": _pair(sample[1]),
        # Universe.Interaction.point_cnot_sample
        "sample.10": _pair(sample[2]),
        # Universe.Interaction.point_cnot_sample
        "sample.11": _pair(sample[3]),
        # Universe.Interaction.point_cnot_sample
        "sample.w0": _real(sample_weights[0]),
        # Universe.Interaction.point_cnot_sample
        "sample.w1": _real(sample_weights[1]),
        # Universe.Interaction.point_cnot_sample
        "sample.w2": _real(sample_weights[2]),
        # Universe.Interaction.point_cnot_sample
        "sample.w3": _real(sample_weights[3]),
        # Universe.Angle.angle_add_cos
        "tempo.add.cos": _real(add_cos),
        # Universe.Angle.angle_add_sin
        "tempo.add.sin": _real(add_sin),
        # Universe.Angle.circle_eight
        "tempo.c8": _real(cosine),
        # Universe.Angle.remainder_half
        "tempo.cap": _real(cap),
        # Universe.Angle.circle_eight
        "tempo.gap8": _real(gap),
        # Universe.Angle.group_half
        "tempo.gcos": _real(group_cos),
        # Universe.Angle.group_half
        "tempo.grem": _real(group_bound),
        # Universe.Angle.group_half
        "tempo.gsin": _real(group_sin),
        # Universe.Angle.angle_half
        "tempo.half.0": _pair(half_0),
        # Universe.Angle.angle_half
        "tempo.half.1": _pair(half_1),
        # Universe.Angle.angle_half
        "tempo.half.c": _real(half_c),
        # Universe.Angle.angle_half
        "tempo.half.gap": _real(half_gap),
        # Universe.Angle.angle_half
        "tempo.half.p0": _real(half_p0),
        # Universe.Angle.angle_half
        "tempo.half.p1": _real(half_p1),
        # Universe.Angle.angle_half
        "tempo.half.rem": _real(half_rem),
        # Universe.Angle.angle_half
        "tempo.half.s": _real(half_s),
        # Universe.Angle.remainder_half
        "tempo.rem4": _real(rest),
        # Universe.Angle.circle_eight
        "tempo.rem8": _real(bound),
        # Universe.Angle.circle_eight
        "tempo.s8": _real(sine),
        # Universe.Symmetry.point_u_row0
        "u.00": _pair(matrix[0][0]),
        # Universe.Symmetry.point_u_row0
        "u.01": _pair(matrix[0][1]),
        # Universe.Symmetry.point_u_row1
        "u.10": _pair(matrix[1][0]),
        # Universe.Symmetry.point_u_row1
        "u.11": _pair(matrix[1][1]),
        # Universe.Observer.point_undone
        "undone.coh": _pair(friend.undone_coherence),
        # Universe.Observer.point_undone
        "undone.purity": _pair(friend.undone_purity),
        # Universe.Symmetry.point_conj_evolution
        "v.0": _pair(change.image[0]),
        # Universe.Symmetry.point_conj_evolution
        "v.1": _pair(change.image[1]),
        # Universe.Symmetry.point_conj_evolution
        "v.conj.0": _pair(change.conjugated[0]),
        # Universe.Symmetry.point_conj_evolution
        "v.conj.1": _pair(change.conjugated[1]),
        # Universe.Symmetry.point_conj_born
        "v.w0": _pair(change.weights[0]),
        # Universe.Symmetry.point_conj_born
        "v.w1": _pair(change.weights[1]),
    }
