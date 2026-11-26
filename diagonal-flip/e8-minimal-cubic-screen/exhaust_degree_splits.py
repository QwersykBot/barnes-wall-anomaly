#!/usr/bin/env python3
"""Exhaust integer degree decompositions and Sym^2/exterior^2 splits.

Published degree lists are parsed as data. No GAP execution or power maps.
Replay: python exhaust_degree_splits.py E82deg.g result.json
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

URL = "https://www.math.rwth-aachen.de/~Frank.Luebeck/chev/E82deg.g"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degrees_source", type=Path)
    parser.add_argument("inner_products", type=Path)
    args = parser.parse_args()
    raw = args.degrees_source.read_bytes()
    match = re.fullmatch(r"\s*degreesE82\s*:=\s*(\[[\s,0-9]*\])\s*;\s*",
                         raw.decode("ascii"))
    if match is None:
        raise ValueError("Unexpected degree-file syntax")
    degrees = json.loads(match[1])
    assert len(degrees) == 1156
    assert all(type(x) is int and x > 0 for x in degrees)
    prior_raw = args.inner_products.read_bytes()
    prior = json.loads(prior_raw)
    assert prior["checks_passed"] is True
    assert prior["classes"] == len(degrees)
    for k in (2, 3):
        assert prior["tensor_power_invariant_dimensions"][str(k)] == {
            "numerator": "1", "denominator": "1"}
    d = prior["degree"]
    census = Counter(x for x in degrees if x <= d*d)
    assert census[1] == census[d] == 1
    extra = sorted(set(census) - {1, d})
    assert extra
    pivot, descending = extra[0], extra[:0:-1]
    target = d*d - 1 - d
    tensor_solutions = []
    leaves = 0

    def tensors(i, residual, chosen):
        nonlocal leaves
        if i == len(descending):
            leaves += 1
            quotient, remainder = divmod(residual, pivot)
            if remainder == 0:
                counts = {1: 1, d: 1, pivot: quotient, **chosen}
                assert sum(k*v for k, v in counts.items()) == d*d
                tensor_solutions.append(counts)
            return
        degree = descending[i]
        for multiplicity in range(residual // degree + 1):
            tensors(i+1, residual-degree*multiplicity,
                    {**chosen, degree: multiplicity})

    tensors(0, target, {})
    sym_dimension, alt_dimension = d*(d+1)//2, d*(d-1)//2
    possibilities = []
    split_leaves = 0
    for tensor in tensor_solutions:
        splits = []

        def split(i, residual, chosen):
            nonlocal split_leaves
            if residual < 0:
                return
            if i == len(descending):
                split_leaves += 1
                quotient, remainder = divmod(residual, pivot)
                if remainder == 0 and quotient <= tensor[pivot]:
                    sym = {**chosen, pivot: quotient}
                    alt = {k: v-sym[k] for k, v in tensor.items()}
                    assert all(x >= 0 for x in alt.values())
                    assert sum(k*v for k, v in sym.items()) == sym_dimension
                    assert sum(k*v for k, v in alt.items()) == alt_dimension
                    splits.append({"symmetric_square": sym, "exterior_square": alt})
                return
            degree = descending[i]
            for multiplicity in range(min(tensor[degree], residual//degree)+1):
                split(i+1, residual-degree*multiplicity,
                      {**chosen, degree: multiplicity})

        # Do not assume either the bilinear-form sign or V's placement.
        for trivial_in_sym in (0, 1):
            for v_in_sym in (0, 1):
                split(0, sym_dimension-trivial_in_sym-d*v_in_sym,
                      {1: trivial_in_sym, d: v_in_sym})
        possibilities.append({"tensor_square": tensor, "all_dimension_splits": splits})

    all_splits = [s for p in possibilities for s in p["all_dimension_splits"]]
    report = {
        "source_url": URL,
        "source_bytes": len(raw),
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "inner_product_receipt_sha256": hashlib.sha256(prior_raw).hexdigest(),
        "analysis_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "published_irreducible_count": len(degrees),
        "degree": d,
        "tensor_square_dimension": d*d,
        "symmetric_square_dimension": sym_dimension,
        "exterior_square_dimension": alt_dimension,
        "small_degrees_with_published_multiplicities": dict(sorted(census.items())),
        "known_tensor_multiplicities": {1: 1, d: 1},
        "tensor_residual_division_leaves": leaves,
        "tensor_square_degree_solutions": len(tensor_solutions),
        "split_residual_division_leaves": split_leaves,
        "compatible_dimension_splits": len(all_splits),
        "all_possibilities": possibilities,
        "trivial_in_symmetric_square_for_every_split": bool(all_splits) and all(
            s["symmetric_square"][1] == 1 for s in all_splits),
        "V_in_symmetric_square_for_every_split": bool(all_splits) and all(
            s["symmetric_square"][d] == 1 for s in all_splits),
        "scope": "Exhaustive degree constraints, conditional on the complete published list and checked tensor inner products",
        "limitations": "Does not construct a VOA group action or prove equivariance of a proposed product",
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
