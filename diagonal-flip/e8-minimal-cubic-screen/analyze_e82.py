#!/usr/bin/env python3
"""Exact tensor-power invariant counts from Luebeck's E82cl.g as DATA.

No GAP execution, symbolic character-table reconstruction, or power maps.
Replay: python analyze_e82.py E82cl.g
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

URL = "https://www.math.rwth-aachen.de/~Frank.Luebeck/chev/E82cl.g"
NAMES = ("orderE82", "centordE82", "valuesMinimalCharacterE82")


def read_data(raw):
    text = raw.decode("ascii")
    text = re.sub(r"#[^\n]*", "", text)
    assignment = re.compile(
        r"\s*(orderE82|centordE82|valuesMinimalCharacterE82)\s*:=\s*"
        r"([0-9]+|\[[\s,0-9-]*\])\s*;"
    )
    values, pos = {}, 0
    while text[pos:].strip():
        match = assignment.match(text, pos)
        if match is None or match[1] in values:
            raise ValueError("Unexpected syntax or duplicate assignment")
        values[match[1]] = json.loads(match[2])
        pos = match.end()
    if set(values) != set(NAMES):
        raise ValueError("Missing or unexpected data assignments")
    return (values[name] for name in NAMES)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    args = parser.parse_args()
    raw = args.source.read_bytes()
    order, centralizers, character = read_data(raw)
    assert type(order) is int and order > 0
    assert len(centralizers) == len(character) == 1156
    assert all(type(c) is int and c > 0 and order % c == 0
               for c in centralizers)
    assert all(type(v) is int for v in character)
    assert centralizers[0] == order and character[0] == 545925250
    sums = {
        k: sum((Fraction(v ** k, c)
                for c, v in zip(centralizers, character)), Fraction(0))
        for k in range(4)
    }
    assert sums[0] == 1, "Class sizes do not sum to group order"
    assert sums[1] == 0, "Nontrivial-character orthogonality failed"
    assert sums[2] == 1, "Real irreducible-character norm failed"
    assert sums[3].denominator == 1 and sums[3] >= 0
    report = {
        "source_url": URL,
        "source_bytes": len(raw),
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "analysis_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "parser": "Strict integer assignments and JSON integer lists; no GAP execution",
        "arithmetic": "Python standard-library fractions.Fraction; exact rationals",
        "classes": len(centralizers),
        "group_order": str(order),
        "degree": character[0],
        "first_three_character_values": character[:3],
        "all_centralizer_orders_divide_group_order": True,
        "class_size_sum": str(sum(order // c for c in centralizers)),
        "tensor_power_invariant_dimensions": {
            str(k): {"numerator": str(v.numerator), "denominator": str(v.denominator)}
            for k, v in sums.items()
        },
        "checks_passed": True,
        "scope": "Tensor powers of the published real-valued irreducible character",
        "not_established": [
            "Symmetric-cube or exterior-cube multiplicity (power maps not used)",
            "An E8(2) action or equivariance on any VOA"
        ],
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
