#!/usr/bin/env python3
"""Exact finite q-series receipt for the c=128 diagonal-flip character.

Mathematical inputs, proved in the accompanying construction note:
  * a holomorphic character has scalar S multiplier 1 and T multiplier
    exp(-2*pi*i/3), with leading exponent -16/3;
  * its coefficients in weights 0..5 are
    [1, 0, 1, 1, 545925252, 545925252].

Set f=E4/eta^8 and j=E4^3/eta^24.  Each f*j^k is holomorphic in the
upper half-plane with the required multiplier.  Choose its degree-five
polynomial to match weights 0..5.  Uniqueness follows by cubing the
difference: a modular function holomorphic on the compactified modular
curve and zero at its cusp vanishes.  No character equality with another
VOA is an input.

Only Python's standard library and exact integers are used.  Output is
JSON; redirect it to character-low-weights.json to reproduce the receipt.
"""

import json
from math import comb


MAX_WEIGHT = 8
POLAR = [1, 0, 1, 1, 545925252, 545925252]


def multiply(left, right):
    result = [0] * (MAX_WEIGHT + 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right[: MAX_WEIGHT + 1 - i]):
            result[i + j] += a * b
    return result


def power(series, exponent):
    result = [1] + [0] * MAX_WEIGHT
    for _ in range(exponent):
        result = multiply(result, series)
    return result


def inverse_euler_product(exponent):
    """Coefficients of product_(n>=1) (1-q^n)^(-exponent)."""
    result = [1] + [0] * MAX_WEIGHT
    for n in range(1, MAX_WEIGHT + 1):
        factor = [0] * (MAX_WEIGHT + 1)
        for k in range(MAX_WEIGHT // n + 1):
            factor[n * k] = comb(exponent + k - 1, k)
        result = multiply(result, factor)
    return result


e4 = [1] + [
    240 * sum(d**3 for d in range(1, n + 1) if n % d == 0)
    for n in range(1, MAX_WEIGHT + 1)
]
F = multiply(e4, inverse_euler_product(8))       # q^(1/3) f
J = multiply(power(e4, 3), inverse_euler_product(24))  # q j

character = [0] * (MAX_WEIGHT + 1)
polynomial = {}
for shift, target in enumerate(POLAR):
    degree = 5 - shift
    basis = ([0] * shift + multiply(F, power(J, degree)))[: MAX_WEIGHT + 1]
    assert basis[shift] == 1
    coefficient = target - character[shift]
    polynomial[str(degree)] = coefficient
    character = [a + coefficient * b for a, b in zip(character, basis)]

assert character[:6] == POLAR

primary4 = character[4] - 2
primary6 = character[6] - 4 - 2 * primary4
twisted6 = (2**28) * 141988
trace4 = character[4] - 2 * (2**28) - 2
trace6 = character[6] - 2 * twisted6 - 4 - 2 * trace4
quotient, remainder = divmod(primary6 - trace6, primary4 - trace4)
assert remainder == 0

print(json.dumps({
    "input_coefficients_weights_0_to_5": POLAR,
    "polynomial_in_j_coefficients_by_degree": polynomial,
    "character_coefficients_weights_0_to_8": character,
    "primary4_dimension": primary4,
    "primary6_dimension": primary6,
    "quantum_involution_trace_primary4": trace4,
    "quantum_involution_trace_primary6": trace6,
    "hypothetical_multiplicity_primary4_in_primary6": quotient,
    "hypothetical_trivial_multiplicity_primary6": primary6 - quotient * primary4,
}, indent=2, sort_keys=True))
