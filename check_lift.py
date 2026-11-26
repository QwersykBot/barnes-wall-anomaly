"""Independent exact audit of the BW(7) quaternion lift candidate.

This checker does not import q16_lift_probe.py and does not use NumPy.  It
constructs Pauli matrices directly from KRR (A.2.5--6), and then constructs
g=(I+X_1 Z_1)(X_3+Z_3)/2 in the lattice basis.  All arithmetic is either
arbitrary-precision integer arithmetic or packed arithmetic over F_2.

The assertions verify a finite lattice/sign certificate, not by themselves
the cohomological or orbifold-construction part of the proposed theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


if not __debug__:
    raise SystemExit("Certificate checks require assertions: run Python without -O or -OO.")


M = 7
N = 1 << M


def add(A, B):
    out = []
    for a, b in zip(A, B):
        row = dict(a)
        for j, value in b.items():
            row[j] = row.get(j, 0) + value
        out.append({j: v for j, v in row.items() if v})
    return out


def multiply(A, B):
    out = []
    for a in A:
        row = {}
        for j, value in a.items():
            for k, value2 in B[j].items():
                row[k] = row.get(k, 0) + value * value2
        out.append({j: v for j, v in row.items() if v})
    return out


def power(A, k):
    out = identity()
    for _ in range(k):
        out = multiply(out, A)
    return out


def identity(sign=1):
    return [{i: sign} for i in range(N)]


def source_pauli(a, kind):
    """a is one-based, as in KRR Appendix A.2."""
    bit = 1 << (M - a)
    result = []
    for i in range(N):
        parity = (M - i.bit_count()) & 1
        if kind == 'X':
            row = {i: 1} if i & bit else {i: -1, i + bit: 1 << parity}
        elif kind == 'Z':
            row = {i: -1, i - bit: 1 << parity} if i & bit else {i: 1}
        else:
            raise ValueError(kind)
        result.append(row)
    return result


def source_gram():
    """Inner product from A.1.1: d_i*d_j*2^|i intersect j|/16."""
    d = [1 << ((M - i.bit_count() + 1) // 2) for i in range(N)]
    denominator = 1 << ((M + 1) // 2)
    G = []
    for i in range(N):
        row = []
        for j in range(N):
            numerator = d[i] * d[j] * (1 << (i & j).bit_count())
            assert numerator % denominator == 0
            row.append(numerator // denominator)
        G.append(row)
    assert all(G[i][i] % 2 == 0 for i in range(N))
    # The scaled lower triangular generator matrix has determinant one.
    assert sum((M - i.bit_count() + 1) // 2 for i in range(N)) == N * ((M + 1) // 2) // 2
    return G


def isometry(A, G):
    return all(
        sum(a * b * G[k][ell] for k, a in A[i].items() for ell, b in A[j].items()) == G[i][j]
        for i in range(N) for j in range(N)
    )


def one_bits(x):
    while x:
        y = x & -x
        yield y.bit_length() - 1
        x ^= y


def parity_transform(x, rows):
    result = 0
    for i in one_bits(x):
        result ^= rows[i]
    return result


class SignLift:
    def __init__(self, A, H):
        self.rows = [sum(1 << j for j, value in row.items() if value & 1) for row in A]
        self.B = []
        for i in range(N):
            # Packed row of R H, with all entries reduced modulo 2.
            rh = parity_transform(self.rows[i], H)
            row = 0
            for j in range(N):
                defect = ((H[i] >> j) & 1) ^ ((rh & self.rows[j]).bit_count() & 1)
                if i == j:
                    assert defect == 0
                elif i > j and defect:
                    row |= 1 << j
            self.B.append(row)
        # Verify that B+B^t is exactly H-R H R^t, so the phase really
        # lifts the twisted group algebra multiplication.
        for i in range(N):
            rh = parity_transform(self.rows[i], H)
            for j in range(N):
                defect = ((H[i] >> j) & 1) ^ ((rh & self.rows[j]).bit_count() & 1)
                assert defect == (((self.B[i] >> j) ^ (self.B[j] >> i)) & 1)

    def apply(self, x):
        sign = 0
        for i in one_bits(x):
            sign ^= (self.B[i] & x).bit_count() & 1
        return sign, parity_transform(x, self.rows)


def lift_word(x, word):
    phase = 0
    for lift in word:
        sign, x = lift.apply(x)
        phase ^= sign
    return phase, x


def dense(A):
    return [[row.get(j, 0) for j in range(N)] for row in A]


def digest(data):
    return hashlib.sha256(json.dumps(data, separators=(',', ':')).encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON report path")
    args = parser.parse_args()
    I, z = identity(), identity(-1)
    X = [source_pauli(a, 'X') for a in range(1, M + 1)]
    Z = [source_pauli(a, 'Z') for a in range(1, M + 1)]
    a = multiply(X[0], Z[0])
    b = multiply(multiply(Z[0], X[1]), Z[1])
    g_numerator = multiply(add(I, a), add(X[2], Z[2]))
    assert all(value % 2 == 0 for row in g_numerator for value in row.values())
    g = [{j: value // 2 for j, value in row.items()} for row in g_numerator]
    G = source_gram()
    for A in X + Z + [g, a, b]:
        assert isometry(A, G)
    assert power(g, 2) == a
    assert power(a, 2) == power(b, 2) == z
    assert multiply(multiply(multiply(b, g), b), g) == z
    assert power(g, 4) == z and power(g, 8) == I
    assert multiply(a, b) != multiply(b, a)
    assert multiply(multiply(multiply(a, b), a), b) == z
    # Explicitly establish that the generated lattice matrix group has
    # 16 elements; a surjection from Q16 therefore has no hidden quotient.
    normal_forms = [power(g, k) for k in range(8)]
    normal_forms += [multiply(power(g, k), b) for k in range(8)]
    assert len({digest(dense(A)) for A in normal_forms}) == 16

    H = [sum(1 << j for j in range(N)
             if ((G[i][j] if i > j else G[i][i] // 2 if i == j else 0) & 1))
         for i in range(N)]
    lx = [SignLift(A, H) for A in X]
    lz = [SignLift(A, H) for A in Z]
    lg = SignLift(g, H)
    # Coefficient-level verification of the exterior-algebra standardness
    # lemma: the only phase terms are complementary pairs of the last
    # six bits, restricted to odd subsets (KRR parity-zero coordinates).
    phase_monomial_counts = []
    rest_mask = (1 << (M - 1)) - 1
    for a_index in range(M):
        factor_bit = 1 << (M - 1 - a_index)
        for kind, lift in [('X', lx[a_index]), ('Z', lz[a_index])]:
            expected_B, expected_rows = [], []
            for i in range(N):
                j = i ^ rest_mask
                parity_zero = (M - i.bit_count()) % 2 == 0
                first_phase = (a_index == 0 and parity_zero
                               and bool(i & (1 << (M - 1))) == (kind == 'Z')
                               and i > j)
                expected_B.append((1 << j) if first_phase else 0)
                row = 1 << i
                if parity_zero and bool(i & factor_bit) == (kind == 'Z'):
                    row ^= 1 << (i ^ factor_bit)
                expected_rows.append(row)
            assert lift.B == expected_B, (a_index + 1, kind, 'phase')
            assert lift.rows == expected_rows, (a_index + 1, kind, 'exterior action')
            phase_monomial_counts.append(sum(row.bit_count() for row in lift.B))
    aw = [lx[0], lz[0]]
    bw = [lz[0], lx[1], lz[1]]
    relations = [
        ('g_squared_equals_prescribed_a', [lg, lg], aw),
        ('b_g_b_g_equals_canonical_z', bw + [lg] + bw + [lg], []),
        ('prescribed_a_squared_equals_canonical_z', aw + aw, []),
        ('prescribed_b_squared_equals_canonical_z', bw + bw, []),
    ]
    tested = 0
    for weight in (1, 2):
        for support in itertools.combinations(range(N), weight):
            vector = sum(1 << i for i in support)
            for name, left, right in relations:
                assert lift_word(vector, left) == lift_word(vector, right), (name, support)
            tested += 1
    # Each phase difference is a polynomial of degree at most two in
    # lattice coordinates modulo two, with constant term zero.  Agreement
    # at every e_i and e_i+e_j proves agreement for every lattice vector.
    assert tested == N + N * (N - 1) // 2

    # Check characteristic polynomial without numeric diagonalization.
    # g^4=-I gives roots among the four primitive eighth roots.  Their
    # multiplicities follow from trace(g)=trace(g^2)=0 and reality.
    traces = [sum(power(g, k)[i].get(i, 0) for i in range(N)) for k in range(1, 5)]
    assert traces == [0, 0, 0, -N]
    assert N % 4 == 0
    rho_numerator = (N // 4) * sum(j * (8 - j) for j in (1, 3, 5, 7))
    rho_denominator = 4 * 64
    assert rho_numerator == 1408 and rho_denominator == 256
    assert (64 * rho_numerator) % (8 * rho_denominator) == 0

    report = {
        'scope': 'Independent exact lattice and VOA-sign-lift certificate; cohomology and orbifold theorem are separate mathematical inputs.',
        'construction': 'Pauli lattice matrices from KRR A.2.5--6, sparse integer g=(I+X1Z1)(X3+Z3)/2; no import of originating checker.',
        'arithmetic': 'Python arbitrary-precision integers and packed F2; no floating-point operations in checks.',
        'rank': N,
        'gram_even_unimodular_from_triangular_basis': True,
        'all_17_source_and_candidate_isometries_exact': True,
        'quaternion_matrix_relations_exact': True,
        'generated_lattice_group_order': 16,
        'lift_coboundary_identity_verified': True,
        'all_generator_phases_match_complementary_pair_quadratics': True,
        'generator_phase_monomial_counts_X1_Z1_then_factor_order': phase_monomial_counts,
        'all_generator_binary_actions_match_wedge_contraction_on_parity_zero': True,
        'phase_inputs_basis_and_pairwise_sums': tested,
        'complete_lift_relations': {name: True for name, _, _ in relations},
        'canonical_g_needs_no_character_correction': True,
        'g_lift_order': 8,
        'g_fixed_lattice_rank': 0,
        'g_standard_lift': True,
        'g_traces_powers_1_to_4': traces,
        'g_primitive_eighth_root_multiplicities': {'1': 32, '3': 32, '5': 32, '7': 32},
        'g_twisted_vacuum_weight': '11/2',
        'g_cyclic_type_mod_8': 0,
        'sha256_compact_dense_g': digest(dense(g)),
        'sha256_compact_dense_b': digest(dense(b)),
        'sha256_compact_dense_gram': digest(G),
        'finite_certificate_verified': True,
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
