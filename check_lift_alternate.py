"""Alternative exact-integer reconstruction of the fixed BW(7) lift certificate.

This was developed separately from check_lift.py.  It starts with Cartesian
Pauli matrices and converts them by the subset/Mobius lattice basis.
NumPy int64 is used here; the main checker instead uses arbitrary-precision
stdlib arithmetic.  No solver, search, timeout, or external data are used.
"""

from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np

if not __debug__:
    raise SystemExit("Certificate checks require assertions: run Python without -O or -OO.")

def basis(m):
    """W = D*Z/sqrt(2^ceil(m/2)), KRR (A.1.1)."""
    n = 1 << m
    zeta = np.array([[int(j & i == j) for j in range(n)] for i in range(n)], dtype=np.int64)
    mobius = np.array([
        [(-1) ** ((i ^ j).bit_count()) if j & i == j else 0 for j in range(n)]
        for i in range(n)
    ], dtype=np.int64)
    d = np.array([1 << ((m - i.bit_count() + 1) // 2) for i in range(n)], dtype=np.int64)
    w = d[:, None] * zeta
    gram_num = w @ w.T
    scale = 1 << ((m + 1) // 2)
    assert np.all(gram_num % scale == 0)
    gram = gram_num // scale
    assert np.all(np.diag(gram) % 2 == 0)
    assert np.array_equal(zeta @ mobius, np.eye(n, dtype=np.int64))
    assert 2 * sum((m - i.bit_count() + 1) // 2 for i in range(n)) == n * ((m + 1) // 2)
    return w, mobius, d, gram


def tensor_ops(m):
    n = 1 << m
    ident = np.eye(n, dtype=np.int64)
    xs, zs = [], []
    for a in range(m):
        bit = 1 << (m - 1 - a)
        x = np.zeros((n, n), dtype=np.int64)
        z = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            x[i, i ^ bit] = 1
            z[i, i] = -1 if i & bit else 1
        xs.append(x)
        zs.append(z)
    y1 = xs[0] @ zs[0]
    # sqrt(2)*H on the third tensor factor; g=(I+Y1)*H3/sqrt(2).
    h3_num = xs[2] + zs[2]
    g_num = (ident + y1) @ h3_num
    b = zs[0] @ xs[1] @ zs[1]
    return ident, xs, zs, g_num, b


def to_lattice(cart_num, denom, w, mobius, d):
    numerator = w @ cart_num @ mobius
    divisor = denom * d[None, :]
    assert np.all(numerator % divisor == 0), "not a lattice automorphism"
    return numerator // divisor


class Lift:
    def __init__(self, matrix, h):
        self.matrix = matrix
        defect = (h - matrix @ h @ matrix.T) % 2
        assert np.array_equal(defect, defect.T)
        assert not np.any(np.diag(defect))
        self.b = np.tril(defect, -1)
        assert np.array_equal((self.b + self.b.T) % 2, defect)

    def phase(self, v):
        v = v % 2
        return int(v @ self.b @ v) % 2


def compose_phase(v, lifts):
    result = 0
    for lift in lifts:
        result ^= lift.phase(v)
        v = v @ lift.matrix
    return result, v

def digest(data):
    return hashlib.sha256(json.dumps(data, separators=(",", ":")).encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON report path")
    args = parser.parse_args()
    m, n = 7, 128
    w, mobius, d, gram = basis(m)
    ident, xs, zs, g_num, b_cart = tensor_ops(m)
    cart = xs + zs + [g_num, b_cart]
    mats = [to_lattice(x, 2 if i == 2*m else 1, w, mobius, d) for i, x in enumerate(cart)]
    for matrix in mats:
        assert np.array_equal(matrix @ gram @ matrix.T, gram)
    x, z = mats[:m], mats[m:2*m]
    g, b = mats[-2:]
    a = x[0] @ z[0]
    assert np.array_equal(g @ g, a)
    assert np.array_equal(a @ a, -ident)
    assert np.array_equal(b @ b, -ident)
    assert np.array_equal(b @ g @ b @ g, -ident)
    h = np.tril(gram, -1) + np.diag(np.diag(gram) // 2)
    lx, lz = [Lift(v, h) for v in x], [Lift(v, h) for v in z]
    lg = Lift(g, h)
    phase_counts = []
    for a_index in range(m):
        for kind, lift in [('X', lx[a_index]), ('Z', lz[a_index])]:
            expected = np.zeros((n,n), dtype=np.int64)
            if a_index == 0:
                for i in range(n):
                    j = i ^ 63
                    if i > j and (7-i.bit_count()) % 2 == 0 and bool(i & 64) == (kind == 'Z'):
                        expected[i,j] = 1
            assert np.array_equal(lift.b, expected)
            phase_counts.append(int(np.sum(lift.b)))
    aw = [lx[0], lz[0]]
    bw = [lz[0], lx[1], lz[1]]
    for e in ident:
        pa, ea = compose_phase(e, aw)
        paa, eaa = compose_phase(e, aw + aw)
        pbb, ebb = compose_phase(e, bw + bw)
        pg2, eg2 = compose_phase(e, [lg, lg])
        pbg, ebg = compose_phase(e, bw + [lg] + bw + [lg])
        assert paa == pbb == pbg == 0
        assert np.array_equal(eaa, -e) and np.array_equal(ebb, -e)
        assert np.array_equal(ebg, -e)
        assert pg2 == pa and np.array_equal(eg2, ea)
    # Lift(...) verifies the full cocycle identity.  Each phase difference
    # above is therefore a lattice character; agreement on a basis suffices.
    assert np.array_equal(np.linalg.matrix_power(g, 4), -ident)
    assert np.array_equal(np.linalg.matrix_power(g, 8), ident)
    traces = [int(np.trace(np.linalg.matrix_power(g, k))) for k in range(1,5)]
    assert traces == [0, 0, 0, -n]
    forms = [np.linalg.matrix_power(g,k) for k in range(8)]
    forms += [v @ b for v in forms[:8]]
    assert len({v.tobytes() for v in forms}) == 16
    report = {
        "scope": "Alternative finite lattice/sign certificate only; theoretical inputs are separate.",
        "construction": "Cartesian Pauli matrices converted by the KRR subset/Mobius basis.",
        "arithmetic": "NumPy int64 matrices and exact parity; checked independently by arbitrary-precision main certificate.",
        "rank": n,
        "canonical_g_needs_no_character_correction": True,
        "full_cocycle_identity_and_lift_relations": True,
        "all_generator_phases_match_complementary_pair_quadratics": True,
        "generator_phase_monomial_counts_X1_Z1_then_factor_order": phase_counts,
        "generated_lattice_group_order": 16,
        "g_lift_order": 8,
        "g_traces_powers_1_to_4": traces,
        "g_twisted_vacuum_weight": "11/2",
        "g_cyclic_type_mod_8": 0,
        "sha256_compact_dense_g": digest(g.tolist()),
        "sha256_compact_dense_b": digest(b.tolist()),
        "sha256_compact_dense_gram": digest(gram.tolist()),
        "finite_certificate_verified": True,
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
