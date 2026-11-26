# Concrete faithful quaternion action

Date: 2026-11-26.

**Status: the exact source and all 22 requested type/axiom reports passed in
[public run 45863204593](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45863204593),
with no local warnings or errors and only the standard three axioms.**
An earlier run found a block-predicate elaboration mismatch and a group
rearrangement timeout. The checked repair exposes the predicate and performs
the final rearrangement in a private abstract-group lemma, with explicit unit
arguments and unchanged public statements. No heartbeat budget or imports were
added. The source is
`BarnesWall/KRRQuaternionAction.lean`, SHA256
`5ee6641589238c91f83c5306734c9f99d3823c68cd5f8b012fd989e8a0eeb377`.
The actual generic `QuaternionLift` source signatures were inspected and match
every call in this adapter. That module passed its separate local kernel and
seven-axiom-report check and compiled in the same public integration run.

## Endpoint and convention

`action` has type `QuaternionGroup 4 →* Aut128`, where `Aut128` is the actual
conformal automorphism group of the concrete positive even lattice VOA.
The source derives `Function.Injective action` and the literal images

- `a 1 ↦ gLift`, the canonical lift of `KRRQ16.gUnit`;
- `xa 0 ↦ bLift`, the canonical lift of `KRRQ16.bUnit`;
- `a 2 ↦ aLift`, whose underlying integral matrix is `KRRQ16.a = g*g`;
- `a 4 ↦ centralLift`, whose underlying integral matrix is `-I`.

The first two generator lifts are not inverted. The ordinary action has
`action (xa k) = bLift * gLift^k`, as stated by `action_xa_nat`. Because canonical
lifts are anti-multiplicative, this corresponds to the matrix word `g^k * b`.
It is not an elementwise identification with the raw lift of the standard
matrix normal form `b * g^k`. That latter labelling gives an ordinary action
of the opposite group. The common `Q8` generator images remain literal; no
unqualified agreement assertion is made for differently ordered matrix words.

## Derived hypotheses

`lift_one` uses the existing full-state composition theorem on two identity
matrices and cancels an idempotent automorphism. `pow_isometry` and the internal
block-support induction use the concrete product-closure theorems. `lift_pow`
then follows by natural-number induction, with the multiplication order
handled by `pow_succ'`.

The matrix relation `b*g*b*g = b*b` cancels in the actual matrix-unit group to
`g*b*g = b`. This also explicitly proves the reversed word `g*b*g*b = b^2`.
Two existing canonical anti-composition equations transport the palindrome to
`gLift*bLift*gLift = bLift`, giving the required conjugation relation. The power
relations come from the checked `g^8 = I`, `b^2 = g^4`, and `lift_pow`.

Finally, if `gLift^4 = 1`, `KRRCanonical.matrix_eq_of_lift_eq` would force the
actual integral matrix `-I` to equal `I`. The checked diagonal-entry contradiction
`KRRQ16.neg_one_ne_one` excludes this. The adapter supplies that nontrivial-center
fact to `QuaternionLift.ofRelations_injective`; it does not assume faithfulness
of a matrix-labelled or abstract phase action.

`centralLift` denotes the canonical lift of the actual unit with matrix `-I`.
Equality with an additional prescribed central operator such as `thetaLat` is
deliberately left to the separate central-lift comparison. No full KRR `E` action
is introduced or claimed here.

## Frozen inputs and suggested reports

- `KRRCanonical.lean`: SHA256
  `f1e5306b4014813bbcc26285dc5d642f273d133fef1eb8eec92f732a66c3ca44`.
- `KRRQ16.lean`: SHA256
  `ad4e192fea7666cad289f247ff4ab3b5555b6cc54fe79b40277a1a5a65462b6f`.
- The independently owned generic constructor is consumed with argument order
  `(A B) (hA8) (hB2) (hconj)` and injectivity's additional final premise `hA4`.

The public theorem declarations under `BarnesWall.KRRQuaternionAction` are
`one_isometry`, `lift_one`, `pow_isometry`, `lift_pow`, `aUnit_val`,
`aUnit_isometry`, `centralUnit_val`, `centralUnit_isometry`, `gLift_sq`,
`gLift_four`, `reversed_unit_word`, `gLift_eight`, `bLift_sq`,
`gLift_mul_bLift`, `gLift_four_ne_one`, `action_a_one`, `action_xa_zero`,
`action_a_two`, `action_a_four`, `action_xa_nat`, and `action_injective`.
The `action` definition itself is also a useful axiom-report target.
All these declarations were included in the successful combined probe.
