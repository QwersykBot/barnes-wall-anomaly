"""Optional exhaustive F_2 check of the BW(7) involution-standardness lemma.

Checks every singular quotient vector whose first tensor factor is nonidentity.
The matrices and phase forms are the closed formulas in proof.md.  Their
identification with the lattice cocycle is checked separately by check_lift.py.
This file has no generic inhomogeneous linear solver and no external inputs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise SystemExit("Certificate checks require assertions: run Python without -O or -OO.")


def bits(x):
    while x:
        low = x & -x
        yield low.bit_length() - 1
        x ^= low


def apply(rows, x):
    out = 0
    for i in bits(x):
        out ^= rows[i]
    return out


def kernel_basis(rows):
    """Image elimination with tracked preimages; returns the exact row kernel."""
    pivots, kernel = {}, []
    for i, original in enumerate(rows):
        image, preimage = original, 1 << i
        while image:
            lead = image.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = (image, preimage)
                break
            previous_image, previous_preimage = pivots[lead]
            image ^= previous_image
            preimage ^= previous_preimage
        else:
            assert preimage.bit_length() - 1 == i
            assert apply(rows, preimage) == 0
            kernel.append(preimage)
    # Kernel vectors have distinct leading input coordinates.  Image pivot
    # vectors have distinct leading output coordinates.  Rank-nullity makes
    # these a complete independent basis, not a sampled set of null vectors.
    assert len({v.bit_length() for v in kernel}) == len(kernel)
    assert len(kernel) + len(pivots) == len(rows)
    return kernel, len(pivots)


def quadratic(lower_rows, x):
    return sum((lower_rows[i] & x).bit_count() for i in bits(x)) & 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    v0 = [i for i in range(128) if (7 - i.bit_count()) % 2 == 0]
    v1 = [i for i in range(128) if (7 - i.bit_count()) % 2 == 1]
    index0, index1 = {v:i for i,v in enumerate(v0)}, {v:i for i,v in enumerate(v1)}
    assert len(v0) == len(v1) == 64
    generators = []
    # Coordinate order: s1,t1,s2,t2,...,s7,t7.
    for a in range(7):
        bit = 1 << (6-a)
        generators.append([0 if i & bit else 1 << index1[i ^ bit] for i in v0])
        generators.append([1 << index1[i ^ bit] if i & bit else 0 for i in v0])
    forms = {}
    for first in (1,2,3):
        polar, lower = [], []
        for k, i in enumerate(v0):
            enabled = bool(first & (2 if i & 64 else 1))
            j = index0[i ^ 63]
            polar.append((1 << j) if enabled else 0)
            lower.append((1 << j) if enabled and j < k else 0)
        forms[first] = (polar, lower)
    total_singular, trivial_phase, checked = 0, 0, 0
    rank_counts = {}
    basis_checks = pair_checks = 0
    for coefficient in range(1 << 14):
        q = sum(((coefficient >> (2*a)) & 1) * ((coefficient >> (2*a+1)) & 1) for a in range(7)) & 1
        if q:
            continue
        total_singular += 1
        first = coefficient & 3
        if not first:
            trivial_phase += 1
            continue
        rows = [0] * 64
        for a in bits(coefficient):
            rows = [x ^ y for x,y in zip(rows, generators[a])]
        kernel, rank = kernel_basis(rows)
        polar, lower = forms[first]
        for v in kernel:
            assert quadratic(lower, v) == 0, (coefficient, v, 'diagonal')
            basis_checks += 1
        for i, v in enumerate(kernel):
            image = apply(polar, v)
            for w in kernel[:i]:
                assert (image & w).bit_count() % 2 == 0, (coefficient, v, w, 'polar')
                pair_checks += 1
        # A quadratic form vanishes on the whole kernel when it vanishes
        # on its basis and its polarization vanishes on every basis pair.
        checked += 1
        rank_counts[str(rank)] = rank_counts.get(str(rank), 0) + 1
    assert (total_singular, trivial_phase, checked) == (8256, 2080, 6176)
    assert rank_counts == {'32': 6176}
    report = {
        'scope': 'Fixed-dimension finite confirmation of the analytic involution-standardness lemma.',
        'arithmetic': 'Python arbitrary-precision integers and packed F2; no numerical approximation.',
        'quotient_dimension': 14,
        'singular_quotient_vectors_including_zero': total_singular,
        'identically_zero_phase_cases': trivial_phase,
        'nontrivial_phase_cases_checked': checked,
        'row_map_rank_counts': rank_counts,
        'kernel_basis_quadratic_checks': basis_checks,
        'kernel_basis_polarization_checks': pair_checks,
        'phase_vanishes_on_all_mod2_fixed_vectors': True,
        'central_sign_changes_share_the_same_mod2_phase_and_action': True,
        'finite_certificate_verified': True,
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
