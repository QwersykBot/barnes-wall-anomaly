# Boolean cubics on a split hyperbolic quadric

## Statement and representation

For every integer m ≥ 2, let Q(x,y) = Σᵢ xᵢyᵢ on 2m Boolean coordinates over
`ZMod 2`. A squarefree polynomial F of degree at most three that vanishes at
every input with Q = 0 has a unique affine multiplier:

    F(x,y) = Q(x,y) (δ + Σᵢ βᵢxᵢ + Σᵢ γᵢyᵢ).

`BarnesWall/BooleanCubic.lean` proves both equality of the evaluated functions
and equality of their reduced squarefree coefficient families. A finite
support records the coordinates assigned one; `eval c S` sums `c T` over all
subsets T of S. `degreeLE3` says that coefficients on supports of size greater
than three vanish. `productCoeff` implements multiplication by Q with Boolean
reduction, including the repeated-variable terms contributing βᵢ + γᵢ to the
coefficient of xᵢyᵢ. No quotient polynomial library or fixed-dimension table is
used.

The proof first eliminates coefficients on supports containing no complete
pair. Evaluations on two complete pairs, optionally with one additional
coordinate, establish consistency of the remaining coefficients. The anchors
0 and 1 suffice for existence already at m = 2. A separate argument proves
uniqueness of the affine multiplier from nonsingular inputs.

The cohomology-facing variant assumes vanishing only at nonzero singular
inputs and **explicitly requires `c ∅ = 0`**. This condition supplies the empty
input in the main theorem. It is necessary in the stated uniform range: at
m = 2, the squarefree cubic `(1+x₁+y₁)(1+x₂)(1+y₂)` vanishes at every nonzero
singular input but equals one at the origin, so it cannot equal Q times an
affine function.

## Verification provenance

At Lean 4.35.0-rc3 and Mathlib revision
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24`, the original source passed a local
kernel check in 14.76 seconds with an empty compiler log. A separate run printed
the types and transitive axioms of these eight declarations:

- `eval_injective`
- `coeff_eq_zero_of_pairFree`
- `eval_productCoeff`
- `affine_multiplier_unique`
- `exists_productCoeff`
- `boolean_cubic_factor_unique`
- `boolean_cubic_eval_factor_unique`
- `boolean_cubic_factor_unique_of_nonzero`

All eight reports contained only `propext`, `Classical.choice`, and `Quot.sound`.
The audited original source was 27,941 bytes with SHA256
`65fb392458808a6a5a8e6f3379b1141e777575ffdc9ec0ba4a681e3b5935d9ee`;
the axiom log had SHA256
`7381ffec0b94e5c2fc65db8aa5278f223084abed17e54cd042eed4f9a7c5a378`.
The integrated source adds only the MIT license header and has SHA256
`62c095443c0d7acf2d927490ec5dc409480a467fb3af4ed6fe499a8d09805815`.
The proof body is byte-identical. That exact integration copy and all eight
requested reports passed in
[public run 45863204593](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45863204593)
at commit 316e085ce9a20240c8a1a5a5f1ae0af76b0c39b6. The complete sixteen-module
integration passed, with every source hash and the probe hash verified.
Independent internal source review found no changed
definitions or theorem statements in the compilation repairs. All authorship
and review here were by AI agents; no independent human review is claimed.

## Boundary with the anomaly argument

This module proves a Boolean combinatorial theorem for the split hyperbolic
form. It does not identify cohomological restriction functions with Boolean
cubics, establish their zero constant coefficient, calculate inflation and its
kernel, compute extraspecial-group cohomology, prove quaternion detection, or
deduce the VOA anomaly theorem. Those interfaces remain separate obligations.
The source also makes no claim about unitarity, twisted modules, an orbifold
extension, or its spectrum.
